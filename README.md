# OOPSLA'27 - Precise Type Analysis on JavaScript Language Specifications via Generalized Occurrence Typing

## Introduction

This tool is an extension of **ESMeta**, the **E**CMAScript **S**pecification **Meta**language. ESMeta extracts a mechanized specification from a given version of the ECMAScript/JavaScript specification ([ECMA-262](https://tc39.es/ecma262/)) and performs static type checking on the specification itself. This artifact keeps only the parts of ESMeta that the type analysis needs: specification extraction, compilation to the intermediate representation, control-flow graph construction, the interpreter, and the type checker.

* Previously, ESMeta only performed syntactic refinement, which led to many false alarms due to insufficient information propagation. Occurrence typing was proposed to address this issue but struggled with mutation and non-boolean return types. Our work introduces a new technique using type guards. The evaluation in the paper compares the following settings over 253 versions of ECMA-262:
  - **Base** (`-tycheck:no-refine`): baseline with no refinements.
  - **Syn** (`-tycheck:infer-guard=false`): original ESMeta using only syntactic refinement.
  - **Ours_NoMut** (`-tycheck:syntactic-kill`): emulates *Occurrence Typing Modulo Theories (Kent et al., PLDI 2016)* by skipping refinement on potentially mutated variables.
  - **Ours_Bool** (`-tycheck:use-boolean-guard`): restricts target types to true and false, illustrating the necessity of generalized target types.
  - **Ours_Inval** (`-tycheck:invalidate-call`): drops every field proposition at each call, as in Flow's invalidation.
  - **Ours** (no extra flag): our full type guard implementation. It reduces the average number of false alarms from 191.6 (*Syn*) to 25.3, with an average of 37.9 alarms per version.
  - **Prov** (`-tycheck:provenance`): additionally records provenance information that shows how type guards are derived and applied.

In every setting, the write effect of a callee is applied at its call sites even when the caller uses the declared return type of the callee (`-tycheck:typed-effect`, on by default). Turning it off (`-tycheck:typed-effect=false`) reproduces the behavior of the earlier implementation, which did not apply these effects.

## Build

The build needs JDK 21, sbt, and the ECMA-262 sources. The ECMA-262 sources are a git submodule, which an anonymized archive of this repository does not include. Clone the full repository so that every version in `versions` can be checked out:

```sh
git clone https://github.com/tc39/ecma262 ecma262
git -C ecma262 checkout 0b24a049c11fe0604b1c929772e7cbd671b78492   # ES2024, used by the tests
```

Then set `ESMETA_HOME` to this directory and build the tool:

```sh
export ESMETA_HOME=$(pwd)
export PATH=$ESMETA_HOME/bin:$PATH
sbt assembly
```

`sbt test` runs the regression tests, including `TypeGuardSmallTest` for the type guard rules.

## Running the Type Checker on One Version

The `-extract:target` option checks out the given commit of the `ecma262` submodule, extracts the specification, and runs the analysis:

```sh
esmeta tycheck -tycheck:detail-log -extract:target=d502ea4
```

The results are written to `logs/analyze`:

- `errors`: the list of alarms (type mismatches), one block per alarm.
- `summary`: one line of statistics (iterations, duration, number of alarms, number of guards, and provenance statistics).
- `guards`, `refined`, `types`: the inferred type guards, refined variables, and inferred types.

On `d502ea4` (the first version in `versions`, right after ES2024), the full setting reports 64 alarms.

## Reproducing the Evaluation

### Alarms, precision, and performance (Figures 16 and 17, Table 2)

`benchmark.sh` runs every setting on the 253 versions of ECMA-262 listed in `versions`:

```sh
./benchmark.sh
```

One setting on 253 versions takes from about 30 minutes (Syn, Ours_Inval) to 3 hours (Ours, Prov) on one machine. To run only some settings, comment out the other `doit` lines at the end of the script. `benchmark-test.sh` runs the same loop on the three versions in `versions-test` as a smoke test.

The results are collected in `result/<setting>/summary.tsv`, one row per version, where `<setting>` is one of `base`, `syn`, `pre` (Ours_NoMut), `bool`, `inval`, `our`, and `prov`. The per-version logs are in `result/<setting>/<index>/`. The columns used in the paper are:

- `# errors`: the number of alarms (Figure 11).
- `iter` and `duration (ms)`: the number of iterations and the analysis time (Figure 12).

### From the raw results to the numbers and figures

`eval/result/<setting>/summary.tsv` holds the results of our run of `benchmark.sh` (seven settings, 253 versions). `eval/tp.tsv` gives the number of true positives per version: the 34 specification bugs in Table 2 were classified by hand, and a version counts a bug until the version that fixes it. The scripts in `eval/` need `pandas` and `matplotlib`:

```sh
cd eval
python3 summarize.py    # average alarms, FP, precision, FP reduction, iteration and time ratios
python3 draw_alarm.py   # Figure 11: fig/alarm/*.pdf and fig/prec.pdf
python3 draw_perf.py    # Figure 12: fig/perf/iter.pdf and fig/perf/time.pdf
```

Precision is the average over versions of `TP / # errors`. To regenerate the figures from your own run, copy `result/<setting>/summary.tsv` of `benchmark.sh` into `eval/result/<setting>/` and run the scripts again.

### Provenance heatmaps (Figure 13)

The heatmaps are drawn from the ES2025 version (`2e1eeda`) with provenance tracking:

```sh
esmeta tycheck -tycheck:detail-log -tycheck:provenance -extract:target=2e1eeda
cd logs/analyze
python3 $ESMETA_HOME/scripts/provenance_heatmaps.py --cap-size 16 --cap-leaf 18
```

The script needs `pandas`, `numpy`, and `matplotlib`. The tables that the paper used are in `eval/heatmap/`, so running the script there redraws Figure 13 without rerunning the analysis. It writes `heatmap-size-depth.pdf`, `heatmap-size-leaf.pdf`, and `heatmap-depth-leaf.pdf` into `logs/analyze`. The `--cap-*` options bin the tail of each axis into the last cell, as in the paper.

## Mechanized Soundness Proof

The soundness theorem of the paper (Theorem 4.1) is mechanized in Lean 4 in
`proof/`. To check it:

```sh
cd proof
lake build                      # checks every proof
lake env lean CheckAxioms.lean  # the main theorems use only standard axioms
```

`proof/README.md` maps each definition and figure of the paper to the Lean code,
and `tech-report.pdf` describes the definitions and the proof structure.

## Example Programs for Other Type Checkers

`examples/` contains the programs that mimic the examples of Section 2 in Typed Racket, Flow, and MLsem, with the checker versions and the results. See `examples/README.md`.

## Hardware Dependencies

This tool does not require high-end hardware but benefits from:

- A reasonably fast CPU. Since the analysis is single-threaded, multicore performance is not critical.
- At least 16GB of RAM, with 32GB or more recommended.

Tests were conducted on **Linux** systems with **AMD64** architecture.
