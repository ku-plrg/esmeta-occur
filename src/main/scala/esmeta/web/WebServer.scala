package esmeta.web

import esmeta.cfg.CFG
import esmeta.web.routes.*
import akka.actor.typed.ActorSystem
import akka.actor.typed.scaladsl.Behaviors
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.*
import akka.http.scaladsl.model.HttpMethods.*
import akka.http.scaladsl.server.*
import akka.http.scaladsl.server.Directives.*
import akka.http.scaladsl.model.headers.*
import akka.http.scaladsl.settings.ServerSettings
import akka.pattern.after
import akka.stream.OverflowStrategy
import akka.stream.scaladsl.{Sink, Source}
import scala.concurrent.{Future, Promise}
import scala.concurrent.duration.*
import scala.io.StdIn
import scala.util.{Failure, Success}

class WebServer(cfg: CFG, port: Int) {
  var shutdownByUser = false;
  var currentSystem: Option[ActorSystem[?]] = None

  def run: Unit = {
    up
    StdIn.readLine();
    shutdownByUser = true;
    for (system <- currentSystem) {
      println("Terminating Server...")
      system.terminate()
    }
  }

  def up: Unit = {
    implicit val system = ActorSystem(Behaviors.empty, "esmeta-web")
    // needed for the future flatMap/onComplete in the end
    implicit val executionContext = system.executionContext

    currentSystem.foreach(_.terminate());
    currentSystem = Some(system);

    // exception handler
    val exceptionHandler = ExceptionHandler {
      case e: Throwable =>
        e.printStackTrace
        complete(
          HttpResponse(StatusCodes.InternalServerError, entity = e.toString),
        )
    }

    // permissive CORS without the built-in directive of akka-http 10.6+,
    // which is not published to Maven Central
    val corsHeaders = List(
      `Access-Control-Allow-Origin`.*,
      `Access-Control-Allow-Methods`(GET, POST, PUT, DELETE, HEAD, OPTIONS),
      `Access-Control-Allow-Headers`("*"),
    )
    def cors(route: Route): Route = respondWithHeaders(corsHeaders) {
      concat(options(complete(StatusCodes.OK)), route)
    }

    // root router
    val rootRoute = cors {
      withRequestTimeout(30.seconds) {
        withRequestTimeoutResponse { _ =>
          HttpResponse(
            StatusCodes.ServiceUnavailable,
            entity = "Request timed out",
          )
        } {
          handleExceptions(exceptionHandler)(
            concat(
              pathPrefix("spec")(SpecRoute(cfg)), // spec route
              pathPrefix("exec")(ExecRoute(cfg)), // exec route
              pathPrefix("breakpoint")(BreakpointRoute()), // breakpoint route
              pathPrefix("state")(StateRoute()), // state route
              pathPrefix("meta")(MetaRoute()), // meta route
            ),
          )
        }
      }

    }

    // serial queue with timeout
    val queue = Source
      .queue[(RequestContext, Promise[RouteResult])](
        1024,
        OverflowStrategy.backpressure,
      )
      .mapAsync(1) {
        case (ctx, promise) =>
          val fut = rootRoute(ctx)
          fut.onComplete(promise.complete)
          fut
      }
      .to(Sink.ignore)
      .run()

    // serialized route which handles request in fifo
    val serialRoute: Route = ctx => {
      val promise = Promise[RouteResult]()
      queue.offer((ctx, promise))
      promise.future
    }

    val bindingFuture = Http().newServerAt(ESMETA_HOST, port).bind(serialRoute)

    system.whenTerminated.onComplete {
      case Success(_) =>
        if (shutdownByUser) {
          println("ActorSystem terminated by user.")
        } else {
          println("ActorSystem terminated. Restarting...")
          up
        }
      case Failure(e) =>
        println(s"ActorSystem crashed: $e")
    }

    println(s"Server now online at http://$ESMETA_HOST:$port")
    println("Press RETURN to stop...")
  }
}
