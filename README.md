# Installation

First install `OCaml` and `opam`. Then, install the following packages:

```
opam install mlcuddidl ounit core ppx_sexp_conv sexplib core_bench menhir
```

Once the dependencies installed, the following build commands are available:

* `make`: builds the `Dice.native` file which is used to evaluate `dice` programs.
* `make test`: builds the test suite `Test.native`. It is recommended that you build
  and run this test suite to guarantee that your system is properly configured.
* `make bench`: builds the benchmark suite `Run_bench.native`, which times how long it takes
  to run each of the programs in the `benchmarks/` directory.

# Tutorial
