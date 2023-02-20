<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Cheby

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/Cheby/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/Cheby/actions?query=workflow:"Docker%20CI"




This repository contains Coq-proofs about some basic facts about Chebyshev
polynomials. It started as a branch of the coqrep library and the early 
version history can still be found in the corresponding repository.

An opam file gives the explicit dependency and let you compile the library

```
opam pin add -y -n cheby .
opam install cheby
```

The file CPoly_ex.v contains some examples of what we can do with this library.

## Meta

- Author(s):
  - Florian Steinberg
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [Bignums](https://github.com/coq/bignums) same version as Coq
  - [MathComp ssreflect 1.16 or later](https://math-comp.github.io)
  - [MathComp algebra 1.16 or later](https://math-comp.github.io)
  - [Flocq 4.1 or later](https://gitlab.inria.fr/flocq/flocq.git)
  - [Interval 4.6.1 or later](https://gitlab.inria.fr/coqinterval/interval)
  - [Coquelico 3.3.0 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
- Coq namespace: `cheby`
- Related publication(s): none

## Building and installation instructions

To instead build and install manually, do:

``` shell
git clone https://github.com/thery/Cheby.git
cd Cheby
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



