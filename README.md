# OOPSLA'25 R2 Artifact Evaluation: ESMeta

## Introduction

This tool is an extension of the **ESMeta**, **E**CMAScript **S**pecification **Meta**language. This framework extracts a mechanized specification from a given version of the ECMAScript/JavaScript specification ([ECMA-262](https://tc39.es/ecma262/)) and automatically generates language-based tools. It supports various features, including differential testing and static type checking for the language specification itself. Though this artifact still supports most of the features, the focus below is on performing type checking, as in the paper. 

* Previously, ESMeta only performed syntactic refinement, which led to many false alarms due to insufficient information propagation. Occurrence typing was proposed to address this issue but struggled with mutation and non-boolean return types. Our work introduces a new technique using type guards, which achieves:
  - A substantial reduction in false alarms. Specifically, our tool shows (as seen in Figure 19) that applying our technique dramatically decreases false alarms (red area).
    - (a) **Base** (`-tycheck:no-refine`): baseline with no refinements.
    - (b) **Syn** (`-tycheck:infer-guard=false`): original ESMeta using only syntactic refinement.
    - (c) **Pre** (`-tycheck:use-syntactic-kill`): emulates *Occurrence Typing Modulo Theories (Kent et al., PLDI 2016)* by skipping analysis on potentially mutated variables.
    - (d) **Bool** (`-tycheck:use-boolean-guard`): restricts demanded types to true and false, illustrating the necessity of generalized demanded types.
    - (e) **Ours** (no extra flag): our full type guard implementation, reducing false alarms from an average of 263.63 (original *Syn*) to 26.7.
  - No significant performance degradation, as demonstrated in Figure 20.
  - Provenance information (**Prov**, `-tycheck:provenance`) is automatically extracted to show how type guards are derived and applied, helping readers better understand the specification.

## Hardware Dependencies

This tool does not require high-end hardware but benefits from:

- A reasonably fast CPU. Since the analysis is single-threaded, multicore performance is not critical.
- At least 16GB of RAM, with 32GB or more recommended.

Tests were conducted on **Linux** systems with **AMD64** architecture.

## Getting-Started guide

1. Download a Docker image from [here]().
2. Run a Docker with `docker run -it esmeta`, which gives you an interactive shell.
3. Done. You can execute esmeta with the `esmeta` command, or directly execute the jar(`java -jar bin/esmeta`). 
   * You might want to test the artifact runs well with the esmeta tycheck command - it prints the analysis result of ES2024 with the latest version, which should yield 64 alarms. 
   * Run `./benchmark.sh` or `./benchmark-test.sh` to get a result for the full benchmark. Refer to the paragraph right below. 

## Step-by-Step guide

### Running the benchmark

Run `./benchmark.sh` from the root directory (`/opt/esmeta`) to perform the full benchmark. This takes approximately 3 hours depending on hardware. To perform a quick test, use `./benchmark-test.sh`, which runs on just the first three ECMA-262 versions (around 5 minutes).

This process produces results covering ES2024 up to the latest internal ECMA-262 version, for all experimental settings (base, syn, pre, bool, ours, prov) in the `result/` directory. Each contains analyses of 167 versions, summarized in `summary.tsv`. We recommend opening these files in a spreadsheet tool.

### Manual Execution

If running a benchmark is too slow, or you just need data for a single version of the ECMA-262, you may want to run a single analysis.

In the interactive shell, run `esmeta tycheck {options}`. Useful options include:

- `-tycheck:detail-log`: Generates detailed logs in opt/esmeta/logs/analyze.
  - `summary.yml` provides the overall analysis summary.
  - `errors` lists the alarms.
  - With `-tycheck:provenance`, a `provenance-logs` file is created, detailing provenance for each refinement point.
- `-extract:target={string}`: Specifies the ECMA-262 version by tag or hash.

### Recommend to Check

Please check that those work well:

* Useful options include:
  - `-tycheck:detail-log`: Generates detailed logs in opt/esmeta/logs/analyze.
    - `summary.yml` provides the overall analysis summary.
    - `errors` lists the alarms.
    - With `-tycheck:provenance`, a `/provenance` directory is created, detailing provenance for each refinement point.
  - `-extract:target={string}`: Specifies the ECMA-262 version by tag or hash.

### Reusability Guide

This artifact will be merged into the main ESMeta repository and integrated into the CI/CD for [ECMA-262](https://github.com/tc39/ecma262). ESMeta is designed to provide consistent type checking for the specification with minimal human intervention, so future ECMA-262 updates should require little to no additional effort.

The implementation of our occurrence typing techniques is mainly in `src/main/scala/esmeta/analyzer/tychecker`: `TypeGuard.scala`, `SymTy.scala`, `AbsTransfer.scala`, `AbsValue.scala`, `Effect.scala`.

These files embody the core of our method and closely align with the paper’s formalization.

## Possible change after the Revision

### Kick-the-Tire phase

May require an additional package (Python or GraphViz), but we will set these dependencies on the Docker image accordingly. We expect that reviewers will **not need to make any changes** in this phase.

### Full Review

* We anticipate more substantial changes after the revision:
  - A list of confirmed true positives (real bugs), including PRs and logs.
  - Possible minor adjustments to the evaluation targets.
  - Enhanced figures for direct comparison with the paper.
  - For provenance, refined tree visualizations to better illustrate explainability.


## (REFERENCE ONLY) Relevant part from the Original Document

  * [Installation Guide](#installation-guide)
    + [Download ESMeta](#download-esmeta)
    + [Environment Setting](#environment-setting)
    + [Installation of ESMeta using `sbt`](#installation-of-esmeta-using--sbt-)
  * [Type Analysis on ECMA-262](#type-analysis-on-ecma-262)

## Installation Guide

We explain how to install ESMeta with the necessary environment settings from
scratch. Our framework is developed in Scala, which works on JDK 17+. So before
installation, please install [JDK
17+](https://www.oracle.com/java/technologies/downloads/) and
[sbt](https://www.scala-sbt.org/), an interactive build tool for Scala.


### Download ESMeta
```bash
$ git clone https://github.com/es-meta/esmeta.git
```

### Environment Setting
Insert the following commands to `~/.bashrc` (or `~/.zshrc`):
```bash
# for ESMeta
export ESMETA_HOME="<path to ESMeta>" # IMPORTANT!!!
export PATH="$ESMETA_HOME/bin:$PATH" # for executables `esmeta` and etc.
source $ESMETA_HOME/.completion # for auto-completion
```
The `<path to ESMeta>` should be the absolute path of the ESMeta repository.


### Installation of ESMeta using `sbt`

Please type the following command to 1) update the git submodules, 2) generate
binary file `bin/esmeta`, and 3) apply the `.completion` for auto-completion.

```bash
$ cd esmeta && git submodule update --init && sbt assembly && source .completion
```

If you see the following message, ESMeta is successfully installed:
```bash
$ esmeta
# Welcome to ESMeta v0.6.1 - ECMAScript Specification Metalanguage.
# Please type `esmeta help` to see the help message.
```

## Basic Commands

You can run this framework with the following command:
```bash
$ esmeta <command> <option>* <filename>*
```
It supports the following commands:
- `help` shows help messages.
- `extract` extracts specification model from ECMA-262 (`ecma262/spec.html`).
- `compile` compiles a specification to an IR program.
- `build-cfg` builds a control-flow graph (CFG) from an IR program.
- `tycheck` performs a type analysis of ECMA-262.
- `parse` parses an ECMAScript file.
- `eval` evaluates an ECMAScript file.
- `web` starts a web server for an ECMAScript double debugger.
- `test262-test` tests Test262 tests with harness files (default: tests/test262).
- `inject` injects assertions to check final state of an ECMAScript file.
- `mutate` mutates an ECMAScript program.
- `analyze` analyzes an ECMAScript file using meta-level static analysis. (temporarily removed)
- `dump-debugger` dumps the resources required by the standalone debugger. (for internal use)
- `dump-visualizer` dumps the resources required by the visualizer. (for internal use)

and global options:
- `-silent` does not show final results.
- `-error` shows error stack traces.
- `-status` exits with status.
- `-time` displays the duration time.
- `-test262dir={string}` sets the directory of Test262 (default: `$ESMETA_HOME/tests/test262`).

If you want to see the detailed help messages and command-specific options,
please use the `help` command:
```bash
# show help messages for all commands
$ esmeta help

# show help messages for specific commands with more details
$ esmeta help <command>
```

## Type Analysis on ECMA-262

ESMeta provides a type analysis on ECMA-262 to infer unknown types in the
specification. We introduced its main concept in the [ASE 2021
paper](https://doi.org/10.1109/ASE51524.2021.9678781) with a tool names
[JSTAR](https://github.com/kaist-plrg/jstar), a **J**avaScript **S**pecification
**T**ype **A**nalyzer using **R**efinement. It analyzes types of mechanized
specification by performing type analysis of IRES. We utilized _condition-based
type refinement_ to prune out infeasible types in each branch for enhanced
analysis precision.

If you want to perform a type analysis of
[ES2022](https://262.ecma-international.org/13.0/) (or ES13), the latest
official version of ECMA-262, please type the following command:
```bash
$ esmeta tycheck
# ...
# ========================================
#  tycheck phase
# ----------------------------------------
# - 1806 functions are initial targets.
# - 2372 functions are analyzed in 32493 iterations.
```

You can perform type analysis on other versions of ECMA-262 with the
`-extract:target` option. Please enter any git tag/branch names or commit hash
as an input of the option:
```bash
# analyze types for origin/main branch version of ECMA-262
$ esmeta tycheck -extract:target=origin/main

# analyze types for 2c78e6f commit version of ECMA-262
$ esmeta tycheck -extract:target=2c78e6f
```