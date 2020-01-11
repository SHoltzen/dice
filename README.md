`Dice` is a probabilistic programming language focused on *fast exact inference*
for *discrete* probabilistic programs.

# Installation

First install `OCaml` and `opam`:

* On Ubuntu, use `apt-get install ocaml opam`.
* On Mac, Homebrew contains the necessary packages: `brew install ocaml opam`.

Then, install the following dependencies from `opam`:

```
opam init   # must be performed before installing opam packages
opam install mlcuddidl ounit core ppx_sexp_conv sexplib core_bench menhir
```

Once the dependencies installed, the following build commands are available:

* `make`: builds the `Dice.native` file which is used to evaluate `dice` programs.
* `make test`: builds the test suite `Test.native`. It is recommended that you build
  and run this test suite to guarantee that your system is properly configured.
* `make bench`: builds the benchmark suite `Run_bench.native`, which times how long it takes
  to run each of the programs in the `benchmarks/` directory.

# Quick Start 

We will start with a very simple example. Imagine you have (unfair) two coins
labeled `a` and `b`. Coin `a` has a 30% probability of landing on heads, and
coin `b` has a 80% chance of landing on heads. You flip both coins and observe
that one of them lands heads-side up. What is the probability that 
coin `a` landed heads-side up?

We can encode this scenario in `Dice` as the following program:

```
let a = flip 0.3 in 
let b = flip 0.8 in
let tmp = observe a || b in 
a
```

The syntax of `Dice` is similar to OCaml. Breaking down the elements of this
program:

* The expression `let x = e1 in e2` creates a local variable `x` with value
  specified by `e1` and makes it available inside of `e2`.
* The expression `flip 0.3` is true with probability 0.3 and false with
  probability 0.8. This is how we model our coin flips: a value of true 
  represents a coin landing heads-side up in this case.
* The expression `observe a || b` conditions either `a` or `b` to be true. This
  expression returns `true`. Dice supports logical conjunction (`||`),
  conjunction (`&&`), and negation (`!`).
* The program returns `a`.

You can find this program in `resources/example.dice`, and then you can run it
by using the `Dice.native` executable:

```
> ./Dice.native resources/example.dice
Value	Probability
true	0.348837
false	0.651163
```

This output shows that `a` has a 34.8837% chance of landing on heads.

## Datatypes
In addition to Booleans, `Dice` supports integers and tuples.

### Tuples

Tuples are pairs of values. The following simple example shows tuples being
used:

```
let a = (flip 0.3, (flip 0.8, false)) in
fst (snd a)
```

Breaking this program down:

* `(flip 0.3, (flip 0.8, false))` creates a tuple.
* `snd e` and `fst e` access the first and second element of `e` respectively.

Running this program:

```
> ./Dice.native resources/tuple-ex.dice
Value	Probability
true	0.800000
false	0.200000
```

### Unsigned Integers

`Dice` supports distributions over unsigned integers. An example program:

```
let x = discrete(0.4, 0.1, 0.3) in 
let y = int(3, 1) in 
x + y
```

Breaking this program down:

* `discrete(0.4, 0.1, 0.3)` creates a random integer that is 0 with probability 0.4, 
   1 with probability 0.1, and 3 with probability 0.3.
* `int(3, 1)` creates an integer constant of size 3 and value 1. All integer
  constants in `Dice` must specify their size (i.e., an integer of size 3
  supports values between 0 and 2 inclusive).
* `x + y` adds `x` and `y` together. All integer operations in `Dice` are
  performed modulo the size (i.e., `x + y` is implicitly modulo 3 in this
  case). `Dice` supports the following integer operations: `+`, `*`, `/`, `-`, 
  `==`, `!=`, `<`, `<=`, `>`, `>=`.

Running this program:

```
> ./Dice.native resources/int-ex.dice
Value	Probability
0	0.300000
1	0.400000
2	0.100000
```

## Functions



## More Examples

More example `Dice` programs can be found in the source directories:

* The `src/Tests.ml` file contains many test case programs.
* The `benchmarks/` directory contains example programs that are run during
  benchmarks.

# Syntax

```

```

