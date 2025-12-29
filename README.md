# FSE'26 - Towards Precise Type Analysis on JavaScript Language Specifications via Occurrence Typing

## Introduction

This tool is an extension of the **ESMeta**, **E**CMAScript **S**pecification **Meta**language. This framework extracts a mechanized specification from a given version of the ECMAScript/JavaScript specification ([ECMA-262](https://tc39.es/ecma262/)) and automatically generates language-based tools. It supports various features, including differential testing and static type checking for the language specification itself. Though this artifact still supports most of the features, the focus below is on performing type checking, as in the paper. 

* Previously, ESMeta only performed syntactic refinement, which led to many false alarms due to insufficient information propagation. Occurrence typing was proposed to address this issue but struggled with mutation and non-boolean return types. Our work introduces a new technique using type guards, which achieves:
  - A substantial reduction in false alarms. Specifically, our tool shows (as seen in Figure 19) that applying our technique dramatically decreases false alarms (red area).
    - (a) **Base** (`-tycheck:no-refine`): baseline with no refinements.
    - (b) **Syn** (`-tycheck:infer-guard=false`): original ESMeta using only syntactic refinement.
    - (c) **Pre** (`-tycheck:syntactic-kill`): emulates *Occurrence Typing Modulo Theories (Kent et al., PLDI 2016)* by skipping analysis on potentially mutated variables.
    - (d) **Bool** (`-tycheck:use-boolean-guard`): restricts demanded types to true and false, illustrating the necessity of generalized demanded types.
    - (e) **Ours** (no extra flag): our full type guard implementation, reducing false alarms from an average of 263.63 (original *Syn*) to 26.7.
  - No significant performance degradation, as demonstrated in Figure 20.
  - Provenance information (**Prov**, `-tycheck:provenance`) is automatically extracted to show how type guards are derived and applied, helping readers better understand the specification.

## Hardware Dependencies

This tool does not require high-end hardware but benefits from:

- A reasonably fast CPU. Since the analysis is single-threaded, multicore performance is not critical.
- At least 16GB of RAM, with 32GB or more recommended.

Tests were conducted on **Linux** systems with **AMD64** architecture.
