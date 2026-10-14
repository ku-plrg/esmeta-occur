# OOPSLA'27 - Towards Precise Type Analysis on JavaScript Language Specifications via Occurrence Typing

## Introduction

This tool is an extension of **ESMeta**, the **E**CMAScript **S**pecification **Meta**language. ESMeta extracts a mechanized specification from a given version of the ECMAScript/JavaScript specification ([ECMA-262](https://tc39.es/ecma262/)) and performs static type checking on the specification itself. This artifact keeps only the parts of ESMeta that the type analysis needs: specification extraction, compilation to the intermediate representation, control-flow graph construction, the interpreter, and the type checker.

* Previously, ESMeta only performed syntactic refinement, which led to many false alarms due to insufficient information propagation. Occurrence typing was proposed to address this issue but struggled with mutation and non-boolean return types. Our work introduces a new technique using type guards. The evaluation in the paper compares the following settings over 253 versions of ECMA-262:
  - **Base** (`-tycheck:no-refine`): baseline with no refinements.
  - **Syn** (`-tycheck:infer-guard=false`): original ESMeta using only syntactic refinement.
  - **NoMut** (`-tycheck:syntactic-kill`): emulates *Occurrence Typing Modulo Theories (Kent et al., PLDI 2016)* by skipping refinement on potentially mutated variables.
  - **Ours_Bool** (`-tycheck:use-boolean-guard`): restricts demanded types to true and false, illustrating the necessity of generalized demanded types.
  - **Inval** (`-tycheck:invalidate-call`): drops every field proposition at each call, as in Flow's invalidation.
  - **Ours** (no extra flag): our full type guard implementation. It reduces the average number of false alarms from 193.1 (*Syn*) to 25.9, with an average of 38.5 alarms per version.
  - **Prov** (`-tycheck:provenance`): additionally records provenance information that shows how type guards are derived and applied.

## Usage

Set `ESMETA_HOME` to this directory and build the tool:

```sh
export ESMETA_HOME=$(pwd)
git submodule update --init
sbt assembly
```

Then run the type checker on one version of ECMA-262. The `-extract:target` option checks out the given commit of the `ecma262` submodule:

```sh
bin/esmeta tycheck -tycheck:detail-log -extract:target=d502ea4
```

The analysis results are written to `logs/analyze`. The `errors` file lists the alarms, and the `summary` file gives one line of statistics.

The scripts `benchmark.sh` and `benchmark-test.sh` run every setting above on the versions listed in `versions` (253 commits used in the paper) and `versions-test` (three commits, for a smoke test). The results are collected in `result/<setting>/summary.tsv`. The scripts in `scripts/` draw the provenance heatmaps from the `prov` setting.

## Hardware Dependencies

This tool does not require high-end hardware but benefits from:

- A reasonably fast CPU. Since the analysis is single-threaded, multicore performance is not critical.
- At least 16GB of RAM, with 32GB or more recommended.

Tests were conducted on **Linux** systems with **AMD64** architecture.
