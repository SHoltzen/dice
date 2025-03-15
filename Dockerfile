FROM ocaml/opam

WORKDIR dice

RUN opam switch create 4.14.1

RUN eval $(opam env)

RUN opam depext mlcuddidl

RUN opam pin add dice git+https://github.com/SHoltzen/dice.git#master

