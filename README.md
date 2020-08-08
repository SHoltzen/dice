`Dice` is a probabilistic programming language focused on *fast exact inference*
for *discrete* probabilistic programs.

# Installation

First install `OCaml` and `opam`:

* On Ubuntu, use `apt-get install ocaml opam m4`.
* On Mac, Homebrew contains the necessary packages: `brew install ocaml opam`.

Then, install the following dependencies from `opam`:

```
opam init   # must be performed before installing opam packages
opam switch 4.09  # ocaml 4.09 is required
eval `opam config env`     # optional: add this line to your .bashrc
opam depext mlcuddidl
opam install ounit core ppx_sexp_conv sexplib core_bench menhir ppx_deriving
```

Next, install the BDD library `mlcuddidl`:

```
git clone git@github.com:SHoltzen/mlcuddidil.git
cd mlcuddidl
./configure && make && make install
```

Once the dependencies are installed, the following build commands are available:

* `make`: builds the `Dice.native` file which is used to evaluate `dice` programs.
* `make test`: builds the test suite `Test.native`. It is recommended that you build
  and run this test suite to guarantee that your system is properly configured.
* `make bench`: builds the benchmark suite `Run_bench.native`, which times how long it takes
  to run each of the programs in the `benchmarks/` directory.

# Quick Start 

We will start with a very simple example. Imagine you have two (unfair) coins
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
let x = discrete(0.4, 0.1, 0.5) in 
let y = int(3, 1) in 
x + y
```

Breaking this program down:

* `discrete(0.4, 0.1, 0.3)` creates a random integer that is 0 with probability 0.4, 
   1 with probability 0.1, and 2 with probability 0.3.
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
0	0.500000
1	0.400000
2	0.100000
```

## Functions

`Dice` supports functions for reusing code. A key feature of `Dice` is that 
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

Here is a more complicated example that shows how to use many `Dice` features
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
`AAAA`. Let's use `Dice` to model this.

The following program models this scenario in `Dice`:

```
fun sendChar(key: int(4), observation: int(4)) {
  let gen = discrete(0.5, 0.25, 0.125, 0.125) in    // sample a FooLang character
  let enc = key + gen in                            // encrypt the character
  observe observation == enc
}
// sample a uniform random key: A=0, B=1, C=2, D=3
let key = discrete(0.25, 0.25, 0.25, 0.25) in
// observe the ciphertext CCCC
let tmp = sendChar(key, int(4, 2)) in
let tmp = sendChar(key, int(4, 2)) in
let tmp = sendChar(key, int(4, 2)) in
let tmp = sendChar(key, int(4, 2)) in
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
> ./Dice.native resources/caesar-ex.dice
Value	Probability
0	0.003650
1	0.058394
2	0.934307
3	0.003650
```

This matches our intuition that `2` is the most likely key.

## More Examples

More example `Dice` programs can be found in the source directories:

* The `src/Tests.ml` file contains many test case programs.
* The `benchmarks/` directory contains example programs that are run during
  benchmarks.

# Syntax

The parser for `Dice` is written in [menhir](http://gallium.inria.fr/~fpottier/menhir/) and can be found in `src/Parser.mly`. The
complete syntax for `Dice` in is:

```
ident := ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
binop := +, -, *, /, <, <=, >, >=, ==, !=, &&, ||

expr := 
   (expr)
   | true
   | false
   | int (size, value)
   | discrete(list_of_probabilities) 
   | expr <binop> expr
   | (expr, expr)
   | fst expr
   | snd expr
   | ! expr
   | flip probability
   | observe expr
   | if expr then expr else expr
   | let ident = expr in expr

type := bool | (type, type) | int(size)
arg := ident: type
function := fun name(arg1: type1, ...) { expr }

program := expr 
        | function program
```
