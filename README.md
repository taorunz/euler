# Asymptotic Lower Bound of Euler Totient Function φ

## Overview

This repository contains a Coq proof of:

<img src="https://render.githubusercontent.com/render/math?math=\forall n\geq 2: \quad \frac{\phi(n)}{n} \geq \frac{1}{e^2 \lfloor \log_2 n\rfloor^4}.">

where <img src="https://render.githubusercontent.com/render/math?math=\phi"> is Euler's totient function.

Part of code is modified from [Daniel de Rauglaudre's proof](https://github.com/roglo/coq_euler_prod_form).

## Build Instructions

Compilation requires [Coq](https://coq.inria.fr/) and the [Interval package](http://coq-interval.gforge.inria.fr/). We recommend installing both with the [opam package manager](https://opam.ocaml.org/) using the commands below.
```
opam update
opam install coq coq-interval
```
Run `make` to compile the proofs. We have tested compilation with Coq versions 8.10.1-8.16.1 and Interval versions 4.0.0-4.6.1.

To use this repository as a library, run `opam pin coq-euler htts://github.com/taorunz/euler.git`.
Then, to import files into your Coq project, use `Require Import euler.FILENAME`.
Subsequent updates can be pulled using `opam install coq-euler`.