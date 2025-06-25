package esmeta.util

import scala.collection.mutable.{Map => MMap}
import scala.collection.mutable.{Set => MSet}
import scala.collection.mutable.{Stack, Queue, PriorityQueue, ListBuffer}

case class GeneralGraph[T](
  edge: MMap[T, MSet[T]] = MMap[T, MSet[T]](),
  rev: MMap[T, MSet[T]] = MMap[T, MSet[T]](),
) {
  def apply(x: T): MSet[T] = edge.getOrElse(x, MSet())
  def +=(p: (T, T)): Unit = {
    val (x, y) = p
    edge.getOrElseUpdate(x, MSet()) += y
    rev.getOrElseUpdate(y, MSet()) += x
  }

  def topologicalSort: List[T] = {
    val visited = MSet[T]()
    val stack = Stack[T]()
    def dfs(v: T): Unit = {
      visited += v
      for (w <- this(v))
        if (!visited.contains(w)) dfs(w)
      stack.push(v)
    }
    for (v <- edge.keys) {
      if (!visited.contains(v)) dfs(v)
    }
    stack.toList
  }

  // Kosaraju's algorithm for finding strongly connected components (SCCs)
  def getSCCs: Map[T, Int] =
    val visited = MSet[T]()
    val stack = Stack[T]()
    val sccs = MMap[T, Int]()
    var sccCount = 0

    def dfs1(v: T): Unit = {
      visited += v
      for (w <- this(v))
        if (!visited.contains(w)) dfs1(w)
      stack.push(v)
    }

    def dfs2(v: T): Unit = {
      sccs.getOrElseUpdate(v, sccCount)
      for (w <- rev.getOrElse(v, MSet()))
        if (!sccs.contains(w)) dfs2(w)
    }

    for (v <- edge.keys) {
      if (!visited.contains(v)) dfs1(v)
    }

    while (stack.nonEmpty) {
      val v = stack.pop()
      if (!sccs.contains(v)) {
        sccCount += 1
        dfs2(v)
      }
    }
    sccs.toMap
}
