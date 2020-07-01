# Cheby

This repository contains Coq-proofs about some basic facts about Chebyshev polynomials. It started as a branch of the coqrep library and the early version history can still be found in the corresponding repository.

The dependencies are as follows:
All files are only tested on Coq 8.11.0 and additionally need mathcomp 1.11.0.
Depending on what part you want to use, you will need additional libraries:
For the orthogonality of Chebychev polynomials that is proven in the file 
"Cheby_trigo.v" you need Coquelicot 3.1.0, and for running the Interval
algorithms from "CPoly_I.v" you will need Coq-Interval 4.0.0.

An opam file gives the explicit dependency and let you compile the library

```
opam pin add -y -n cheby .
opam install cheby
```

The file CPoly_ex.v contains some examples of what we can do with this library.
