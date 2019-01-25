# FreeSpec

FreeSpec is a framework for the Coq proof assistant to modularly verify programs
with effects and effect handlers. It relies on the Program monad as defined in
the [`operational` package](https://hackage.haskell.org/package/operational) of
Haskell, and uses so-called abstract specifications to specify, for each effect,
expected properties for the effect result, independently of any underlying
effect handler.

## Overview

This repository is organized as follows:

- `core/`: the core framework that notably introduces `Program`,
  `Semantics` and `Specification`.

FreeSpec formalism has been described in depth in [an academic
paper](https://hal.inria.fr/hal-01799712/document) published at the [Formal
Methods 2018 conference](https://www.win.tue.nl/~evink/FM2018/).

## Getting Started

This repository relies on
[`coq-prelude`](https://github.com/ANSSI-FR/coq-prelude), an “*opinionated
Prelude for Coq inspired by Haskell*”. In particular, `coq-prelude` provides the
Monad-related definitions.  Eventually, we will submit a Pull Request to the Coq
OPAM Repository to add `coq-prelude`. Right now, you need to install this
library from source (see the [appropriate
README](https://github.com/ANSSI-FR/coq-prelude/blob/master/README.md) for
installation notes).

FreeSpec is being developed and tested with the latest Coq release only. We make
no promise regarding older versions.

```bash
# from the root of this repository
cd core/
./configure
make install # regarding your setup, you may need to use `sudo` here
```

Once the framework has been correctly installed, you can have a look at the
example files provided in this repository. They should compile just fine.

```bash
# from the root of this repository
cd examples/
make
```
