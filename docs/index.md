---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
---

# Forbidden Matrix Theory

The purpose of this repository is to *digitise* some mathematical definitions, theorem statements
and theorem proofs. Digitisation, or formalisation, is a process where the source material,
typically a mathematical textbook or a pdf file or website or video, is transformed into definitions
in a target system consisting of a computer implementation of a logical theory (such as set theory
or type theory).

## The source

The definitions, theorems and proofs in this repository are taken from the literature on forbidden
matrix theory.

## The target

The formal system which we are using as a target system is Lean's dependent type theory. Lean is a
project being developed by the [Lean FRO](https://lean-fro.org/).

### Code organisation

The Lean code is contained in the directory `ForbiddenMatrix/`. The subdirectories are:
* `Mathlib`: Material missing from existing mathlib developments
* `Prereqs`: New developments to be integrated to mathlib

### Current progress

The project is not yet finished. The following table details live which files are unfinished, and
how many 'sorries' (unproven statements) remain in each file.

{% include sorries.md %}

Here is the list of files that do not depend on any other ForbiddenMatrix file, indicating they are good candidates for upstreaming to mathlib:

{% include files_to_upstream.md %}

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).
Alternatively, click on the button below to open a Gitpod workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/YaelDillies/ForbiddenMatrix)

In either case, run `lake exe cache get` and then `lake build` to build the project.

## Build the blueprint

See instructions at https://github.com/PatrickMassot/leanblueprint/.

## Acknowledgements

Our project builds on mathlib. We must therefore thank its numerous contributors without whom this
project couldn't even have started.

Much of the project infrastructure has been adapted from
* [sphere eversion](https://leanprover-community.github.io/sphere-eversion/)
* [liquid tensor experiment](https://github.com/leanprover-community/liquid/)
* [unit fractions](https://github.com/b-mehta/unit-fractions/)
