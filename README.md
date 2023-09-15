## Building

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The recommended way is to run the following commands, which create a local opam switch, install dependencies and compile Coq proofs:

```
opam switch create . -y --deps-only --repos default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git
eval $(opam env)
make
```

Alternatively, you can try to install dependencies in the current opam switch and compile Coq proofs:

```
make depend
make
```
