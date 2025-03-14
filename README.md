[![CI - Build and Test](https://github.com/SHoltzen/dice/actions/workflows/ci.yml/badge.svg)](https://github.com/SHoltzen/dice/actions/workflows/ci.yml)

`dice` is a probabilistic programming language focused on *fast exact inference*
for *discrete* probabilistic programs. For more information for how `dice` works
see the research article [here](https://arxiv.org/abs/2005.09089). To cite
`dice`, please use:
```
@article{holtzen2020dice,
  title={Scaling Exact Inference for Discrete Probabilistic Programs},
  author={Holtzen, Steven and {Van den Broeck}, Guy and Millstein, Todd},
  journal={Proc. ACM Program. Lang. (OOPSLA)},
  publisher={ACM},
  doi={https://doi.org/10.1145/342820},
  year={2020}
}
```


# Installation

## Docker

A [docker](https://www.docker.com/) image is available, and can be installed
with:

```
docker pull sholtzen/dice
```


## Building From Source

The following steps set up the environment for building `dice`.
First install `opam` (version 2.0 or higher) following the instructions
[here](https://opam.ocaml.org/doc/Install.html).
Then, install `rust` following the commands [here](https://rustup.rs/).
Then, run the following in your
terminal:

```
opam init                  # must be performed before installing opam packages
opam switch create 4.14.1  # switch to use OCaml version 4.14
eval `opam config env`     # optional: add this line to your .bashrc
source $HOME/.cargo/env    # set up rust environment
git submodule update --init --recursive    # populate the rsdd subdirectory
opam install . --deps-only # install dependencies
```

### Building 

First follow the steps for installation. Then, the following build commands are
available:

* `dune build`: builds the project from source in the current directory.
* `dune exec dice`: runs the `dice` executable.
* `dune test`: runs the test suite
* `dune exec dicebench`: runs the benchmark suite.

# Quick Start 

We will start with a very simple example. Imagine you have two (unfair) coins
labeled `a` and `b`. Coin `a` has a 30% probability of landing on heads, and
coin `b` has a 80% chance of landing on heads. You flip both coins and observe
that one of them lands heads-side up. What is the probability that 
coin `a` landed heads-side up?

We can encode this scenario in `dice` as the following program:

```
let a = flip 0.3 in 
let b = flip 0.8 in
let tmp = observe a || b in 
a
```

The syntax of `dice` is similar to OCaml. Breaking down the elements of this
program:

* The expression `let x = e1 in e2` creates a local variable `x` with value
  specified by `e1` and makes it available inside of `e2`.
* The expression `flip 0.3` is true with probability 0.3 and false with
  probability 0.8. This is how we model our coin flips: a value of true 
  represents a coin landing heads-side up in this case.
* The expression `observe a || b` conditions either `a` or `b` to be true. This
  expression returns `true`. `dice` supports logical conjunction (`||`),
  conjunction (`&&`), equality (`<=>`), negation (`!`), and exclusive-or (`^`).
* The program returns `a`.

You can find this program in `resources/example.dice`, and then you can run it
by using the `dice` executable:

```
> dice resources/example.dice
Value	Probability
true	0.348837
false	0.651163
```

This output shows that `a` has a 34.8837% chance of landing on heads.

## Optimizations

The Dice compiler has the following built-in optimizations and alternative run-time modes 
that are activated with the following flags:

* `-determinism`: replaces deterministic probabilistic choices with non-random choices (i.e., `flip 1.0` becomes `true`). It is recommended that this flag be enabled for most cases.
* `-eager-eval`: changes the compilation order to avoid substitution during compilation. Can perform faster than the default compilation order on certain cases.
* `-flip-lifting`: removes redundant `flip` expressions from certain classes of programs -- can increase performance.

## Datatypes
In addition to Booleans, `dice` supports integers, tuples, and lists.

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
> dice resources/tuple-ex.dice
Value	Probability
true	0.800000
false	0.200000
```

### Unsigned Integers

`dice` supports distributions over unsigned integers. An example program:

```
let x = discrete(0.4, 0.1, 0.5) in 
let y = int(2, 1) in 
x + y
```

Breaking this program down:

* `discrete(0.4, 0.1, 0.5)` creates a random integer that is 0 with probability 0.4, 
   1 with probability 0.1, and 2 with probability 0.3.
* `int(2, 1)` creates a 2-bit integer constant with value 1. All integer
  constants in `dice` must specify their size.
* `x + y` adds `x` and `y` together. All integer operations in `dice` are
  performed modulo the size (i.e., `x + y` is implicitly modulo 4 in this
  case). `dice` supports the following integer operations: `+`, `*`, `/`, `-`, 
  `==`, `!=`, `<`, `<=`, `>`, `>=`.

Running this program:

```
> dice resources/int-ex.dice
Value	Probability
0	0.
1	0.4
2	0.1
3	0.5
```

Various distributions over integers have their own syntax. For instance,
* `uniform(3, 2, 6)` creates a random 3-bit integer, containing a uniform distribution
  over the integers 2, 3, 4, 5.
* `binomial(3, 4, 0.5)` creates a random 3-bit integer, containing a binomial distribution
  with parameters `n=4`, `p=0.5`


### Lists

`dice` supports distributions over lists, possibly of different lengths.

```
let xs = [flip 0.2, flip 0.4] in
if flip 0.5 then (head xs) :: xs else tail xs
```

Breaking this program down:

- `[flip 0.2, flip 0.4]` creates a list of Booleans with two elements.
- `head xs` returns the first element of `xs` and `tail xs` returns a list of everything after the first element.
- `x :: xs` returns a list with `x` added to the front of `xs`.

Running this program:

```
> dice -max-list-length 3 resources/list-ex.dice
Value   Probability
[]      0.
[true]  0.2
[false] 0.3
[true, true]    0.
[true, false]   0.
[false, true]   0.
[false, false]  0.
[true, true, true]      0.04
[true, true, false]     0.06
[true, false, true]     0.
[true, false, false]    0.
[false, true, true]     0.
[false, true, false]    0.
[false, false, true]    0.16
[false, false, false]   0.24
```

## Functions

`dice` supports functions for reusing code. A key feature of `dice` is that 
functions are *compiled once and then reused* during inference.

A simple example program:

```
fun conjoinall(a: bool, b: (bool, bool)) {
  a && (fst b) && (snd b)
}
conjoinall(flip 0.5, (flip 0.1, true))
```

Breaking this program down:

* A function is declared using the syntax `fun name(arg1: type1, arg2: type2, ...) { body }`. 
* A program starts by listing all of its functions. Then, the program has a main body after
  the functions that is run when the program is executed. In this program, the main 
  body is `conjoinall(flip 0.5, (flip 0.1, true))`.
* Right now recursion is not supported.
* Functions do not have `return` statements; they simply return whatever the
  last expression that evaluated returns.

Result of running this program:

```
Value	Probability
true	0.050000
false	0.950000
```

## Caesar Cipher

Here is a more complicated example that shows how to use many `dice` features
together to model a complicated problem.
We will decrypt text that was
encrypted using a [Caesar cipher](http://practicalcryptography.com/ciphers/caesar-cipher/). We can decrypt
text that was encrypted using a Caesar cipher by [frequency analysis](https://en.wikipedia.org/wiki/Frequency_analysis):
using our knowledge of the rate at which English characters are typically in order to 
infer what the underlying key must be.

Consider the following simplified scenario. Suppose we have a 4-letter language called `FooLang`
consisting of the letters `A`, `B`, `C`, and `D`. Suppose that for this language,
the letter `A` is used 50% of the time when spelling a word, `B` is used 25% of the
time, and `C` and `D` are both used 12.5% of the time.

Now, we want to infer the most likely key given after seeing some encrypted
text, using knowledge of the underlying frequency of letter usage. Initially we
assume that all keys are equally likely. Then, we observe some encrypted text:
say the string `CCCC`. Intuitively, the most likely key should be 2: since `A`
is the most common letter, the string `CCCC` is most likely the encrypted string
`AAAA`. Let's use `dice` to model this.

The following program models this scenario in `dice`:

```
fun sendChar(key: int(2), observation: int(2)) {
  let gen = discrete(0.5, 0.25, 0.125, 0.125) in    // sample a FooLang character
  let enc = key + gen in                            // encrypt the character
  observe observation == enc
}
// sample a uniform random key: A=0, B=1, C=2, D=3
let key = discrete(0.25, 0.25, 0.25, 0.25) in
// observe the ciphertext CCCC
let tmp = sendChar(key, int(2, 2)) in
let tmp = sendChar(key, int(2, 2)) in
let tmp = sendChar(key, int(2, 2)) in
let tmp = sendChar(key, int(2, 2)) in
key
```

Now we break this down. First we look at the `sendChar` function:

* It takes two arguments: `key`, which is the underlying secret encryption key, and
  `observation`, which is the observed ciphertext.
* The characters `A,B,C,D` are encoded as integers.
* A random character `gen` is sampled according to the underlying distribution
  of characters in `FooLang`.
* Then, `gen` is encrypted by adding the key (remember, addition occurs modulo 4
  here).
* Then, ciphertext character is observed to be equal to the encrypted character.

Next, in the main program body, we sample a uniform random key and encrypt the
string `CCCC`. Running this program:

```
> dice resources/caesar-ex.dice
Value	Probability
0	0.003650
1	0.058394
2	0.934307
3	0.003650
```

This matches our intuition that `2` is the most likely key.

## More Examples

More example `dice` programs can be found in the source directories:

* The `test/Test.ml` file contains many test case programs.
* The `benchmarks/` directory contains example programs that are run during
  benchmarks.

# Syntax

The parser for `dice` is written in [menhir](http://gallium.inria.fr/~fpottier/menhir/) and can be found in `lib/Parser.mly`. The
complete syntax for `dice` in is:

```
ident := ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
binop := +, -, *, /, <, <=, >, >=, ==, !=, &&, ||, <=>, ^, ::

expr := 
   (expr)
   | ident
   | true
   | false
   | int (size, value)
   | discrete(list_of_probabilities) 
   | uniform(size, start, stop)
   | binomial(size, n, p)
   | expr <binop> expr
   | (expr, expr)
   | fst expr
   | snd expr
   | ! expr
   | flip probability
   | observe expr
   | if expr then expr else expr
   | let ident = expr in expr
   | [ expr (, expr)* ]
   | [] : type
   | head expr
   | tail expr
   | length expr

type := bool | (type, type) | int(size) | list(type)
arg := ident: type
function := fun name(arg1, ...) { expr }

program := expr 
        | function program
```
