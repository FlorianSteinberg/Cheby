# Cheby

This repository contains Coq-proofs about some basic facts about Chebyshev polynomials. It started as a branch of the coqrep library and the early version history can still be found in the corresponding repository.

The dependencies are as follows: All files are only tested on Coq 8.8.0 and additionally need mathcomp 1.7.0.
Depending on what part you want to use, you will need additional libraries: For the orthogonality of Chebychev polynomials that is proven in the file "Cheby_trigo.v" you need Coquelicot 3.0.2, and for running the Interval algorithms from "CPoly_I.v" you will need Coq-Interval 3.3.0.
