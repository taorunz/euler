# Asymptotic Lower Bound of Euler Totient Function φ

## Overview

We proved in Coq:

<img src="https://render.githubusercontent.com/render/math?math=\forall n\geq 2: \quad \frac{\phi(n)}{n} \geq \frac{1}{e^2 \lfloor \log_2 n\rfloor^4}.">

Here <img src="https://render.githubusercontent.com/render/math?math=\phi"> is the Euler's totient function.

Part of code is modified from Daniel de Rauglaudre's proof.

## Compilation

Compilation requires [Coq](https://coq.inria.fr/) and the [Interval package](http://coq-interval.gforge.inria.fr/). We recommend installing both with the [opam package manager](https://opam.ocaml.org/), using the commands below.
```
opam install coq
opam install coq-interval
```
Run `make all' to compile the proofs. We have tested compilation with Coq versions 8.10.1-8.13.2 and Interval versions 4.0.0-4.2.0.