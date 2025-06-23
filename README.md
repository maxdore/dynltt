# ICFP 2025 Artifact

Name:    **Linear Types with Dynamic Multiplicities in Dependent Type Theory (Functional Pearl)**


This folder contains the artefact accompanying the paper "Linear Types with
Dynamic Multiplicities in Dependent Type Theory".

The code has been type-checked with Agda in version 2.7.0.1 and the Cubical
library version 0.8.


## Installation of Agda and Cubical Agda

The artefact has two dependencies. Agda can be installed as follows:

```
apt install ghc cabal-install zlib1g-dev libncurses5-dev
cabal update
cabal install alex happy Agda
```

Further information on (and alternative ways to install) Agda can be found at
`https://agda.readthedocs.io/en/latest/getting-started/installation.html`.


The Cubical library in version 0.8 can be installed as follows:
1. Download the library files from
   `https://github.com/agda/cubical/releases/download/v0.8/cubical-0.8.tar.gz`.
2. Unpack the tarball and register it by creating a file `HOME/.agda/libraries`
   with contents `CUBICAL_DIR/cubical.agda-lib`.

Further information about Agda's library management can be found at
`https://agda.readthedocs.io/en/latest/tools/package-system.html`.


## Usage

All files can be checked by calling `make` (which runs Agda's typechecker on
`Everything`, which includes most files part of the paper, and `Axiomatic`, an
alternative implementation of the basic framework presented in the paper).

The files can be compiled into highlighted, hyperlinked web pages by calling
`make html`. This will create an `html` folder, in which `Everything.html` is a
good starting point to explore the artefact.


## Explanation of files and links to sections in the paper

The code listings in the paper were generated from the present artefact using
the latex backend of Agda, all definitions are hence called exactly the same as
in the paper and should be easily traceable. The code files correspond to the
different sections as follows:

- `Base` contains the main setup of supplies and productions and the linear
  judgment which is explained in Sections 2.1-2.3.
- `Lemmas` contains derivable rules from our system that we need in many
  programs. A few of these lemmas are mentioned in Section 2.2.
- `Functions` contains notation for linear functions and function application
  which is introduced in Sections 2.4 and 4.2.
- `List` contains the different folds and their instances which are introduced
  in Sections 3.1, 3.2 and 4.2.
- `ISort` contains insertion sort explained in Section 3.4.
- `ListPartial` contains the different unfolds and their instances which are
  introduced in Sections 3.3 and 4.3.
- `SSort` contains selection sort explained in Section 3.4.
- `Conat` contains a few examples which use the conatural numbers to capture
  resources as explained in Section 4.4.
- `Vector` contains the vector zip program given in Section 5.
- `Axiomatic` contains the data types that can be used to add our system to
   theories which do not offer higher inductive types, as discussed in Section
   6.1.



## Explanation of flags

- All files make use of Agda's `cubical` mode, except of `Axiomatic`, which
  demonstrates how the construction of the paper can be added in the absence of
  higher inductive types.
- all files have the `safe` flag enabled except of `ListPartial`, `ISort`,
  `SSort` and `Conats` (and consequently also `Everything`). A few definitions
  in `ListPartial` and `Conats` give rise to partial functions, which is why we
  had to turn off Agda's termination checker for these. In contrast, all
  programs in `ISort` and `SSort` are easily seen to be terminating, but the
  structural recursion is on arguments that are part of a pair, which is why
  Agda's termination checker cannot recognise this. We have kept these versions
  of the programs (instead of uncurrying the functions) since they are more
  legible and work more nicely together with the setup of linear functions in
  multiple arguments.
- the `guardedness` flag is enabled in `Conats` (and consequently also
  `Everything`) to allow the use of coinductive data types.
- we disabled the `UnsupportedIndexedMatch` warning in `Order` and `Vector`,
  which signals that some inductive types do not compute when applied to some
  primitives of `cubical` (namely transports). This does not happen in our
  development and is of no concern to us.

