#!/bin/zsh

# a helper function for logging with a timestamp
log() {
  echo -n "[`date +'%Y-%m-%d %H:%M:%S'`] " | tee -a log
  echo $1 | tee -a log
}
run() {
  log "$1"
  eval $1 | tee -a log
}

initdir() {
  local dirname=$1
  rm -rf $dirname
  mkdir $dirname
}

doit() {
  local dirname=$1
  local option=$2

  initdir $dirname
  cd $dirname

  local head="#"
  head+="\tversion"
  head+="\titer"
  head+="\tduration (ms)"
  head+="\t# errors"
  head+="\t# analyzed funcs"
  head+="\t# total funcs"
  head+="\t# analyzed nodes"
  head+="\t# total nodes"
  head+="\t# refined targets"
  head+="\t# refined locals"
  head+="\t# avg. depth"
  head+="\t# guards"
  head+="\t# total provenances"
  head+="\t# avg. prov size"
  head+="\t# avg. prov depth"
  head+="\t# avg. prov leaf"
  run "echo '$head' > summary.tsv"
  local i=0
  for version in $(cat ../../versions); do
    log "[$i] Analyzing $version"
    run "esmeta tycheck -tycheck:detail-log -extract:target=$version $option"
    run "mv $ESMETA_HOME/logs/analyze $i"
    run "echo -n '$i\t$version\t' >> summary.tsv"
    run "cat $i/summary >> summary.tsv"
    run "echo "" >> summary.tsv"
    i=$((i+ 1))
  done

  cd ..
}

initdir result
cd result

doit base "-tycheck:no-refine=true"
doit syn "-tycheck:infer-guard=false"
doit pre "-tycheck:infer-guard=true -tycheck:use-syntactic-kill"
doit bool "-tycheck:use-boolean-guard"
doit our ""
doit prov "-tycheck:infer-guard=true -tycheck:provenance"

cd ..
