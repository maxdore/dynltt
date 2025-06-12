This folder contains code accompanying the paper "Linear Types with Dynamic
Multiplicities in Dependent Type Theory".

The code has been type-checked with Agda in version 2.7.0.1 and the Cubical
library version 0.8. The safe-flag was used for all files except those that
contain partial functions.


## Installation

Agda can be installed as follows:

```
apt install ghc cabal-install zlib1g-dev libncurses5-dev
cabal update
cabal install alex happy Agda
```

The Cubical library can be cloned from GitHub:
```
git clone https://github.com/agda/cubical.git
```

To use the library with Agda, add the library by
1. registering it by creating a file `.agda/libraries` with contents
   `/cubical/cubical.agda-lib` and then
2. making it default by creating a file `.agda/defaults` with contents `cubical`


## Explanation of files

The folder html contains a HTML export of all of the .agda files which allows
for quickly navigating the code.

- `Everything` contains links to all files (except of `Axiomatic`, which uses K)
- `Base` contains the main setup of supplies and productions and the linear judgment
- `Lemmas` contains derivable rules from our system that we need in many programs
- `Functions` contains notation for linear functions and function application
- `List` contains the different folds and their instances
- `ISort` contains insertion sort
- `ListPartial` contains the different unfolds and their instances
- `SSort` contains selection sort
- `Conat` contains a few examples which use the conatural numbers to capture resources
- `Vector` contains the vector zip program
- `Axiomatic` contains the data types that can be used to add our system to theories
   which do not offer higher inductive types, as discussed in Section 6.1.




