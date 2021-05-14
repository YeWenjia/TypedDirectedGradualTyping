# Type-Directed Operational Semantics for Gradual Typing (artifact)

## Abstract

This artifact contains the Coq formulation of \B, \Bg and \Br calculus associated with 
the paper "Type-Directed Operational Semantics for Gradual Typing". This document 
explains how to run the Coq formulations and Coq files briefly. Artifact 
can either be compiled in the pre-built docker image with all the 
dependencies installed or it could be built from the scratch.

# 1) Docker Image #

This section explains how to pull the docker image of artifact from docker repo and use it.
Run the following commands one by one in terminal:

1. `$ docker pull ecoop2021/ecoop2021`
2. `$ docker run -it ecoop2021/ecoop2021`
3. `$ eval $(opam env)`

The artifact is located in /home/coq/ecoop2021/ directory.

There are two folders in the artifact, with make file in each:

1. **Calculus** → contains \B and \Bg formulation
2. **Variant** → contains \Br formulation

Go to each folder and run make:

### Calculus

1. `$ cd /home/coq/ecoop2021/Calculus`
2. `$ eval $(opam env)`
3. `$ make`

### Variant

1. `$ cd /home/coq/ecoop2021/Variant`
2. `$ eval $(opam env)`
3. `$ make`


# 2) Build from Scratch #

This section explains how to build the artifact from scratch

### Prerequisites

1. Install Coq 8.10.2.
   The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.10.2). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command
   not found" this means you have not properly installed Coq), then install `Metalib`:
   1. Open terminal
   2. `git clone https://github.com/plclub/metalib`
   3. `cd metalib/Metalib`
   5. `make install`


### Build and Compile the Proofs

1. Enter  `coq/Calculus` or `coq/Variant`  directory.

2. Please make sure to run the command `eval \$(opam env)` before running make if 
   you installed the Coq via opam. 

3. Type `make` in the terminal to build and compile the proofs.


## Proof Structure

- `Calculus` directory contains the definition and proofs of \B and \Bg
- `Variant` directory contains the definition and proofs of \Br 
- `Calculus/syntax_ott.v` contains the locally nameless definitions of \Bg.
- `Variant/syntax_ott.v` contains the locally nameless definitions of \Br.
- `Calculus/syntaxb_ott.v` contains the locally nameless definitions of \B.
- `rules_inf.v` and `rulesb_inf.v` contains the `lngen` generated code.
- `Infrastructure.v` contains the type systems of the calculi and some lemmas.
- `Infrastructure_b.v` contains the type systems of the blame calculi and some lemmas.
- `Deterministic.v` contains the proofs of the determinism property.
- `Typing.v` contains the proofs of some typing lemmas.
- `Typing_b.v` contains the proofs of some blame calculus typing lemmas.
- `ttyping.v` contains the proofs of some elaboration typing lemmas.
- `criteria.v` contains the proofs of gradual guarantee theorem.
- `Type_Safety.v` contains the proofs of the type preservation and progress properties.
- `soundness.v` contains the proofs of the soundness theorem with respect to blame calculus.
- `soundness_blame.v` contains the proofs of the soundness theorem with respect to blame calculus.
