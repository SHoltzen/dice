FROM ocaml/opam2

WORKDIR dice

RUN opam switch 4.09

RUN opam depext mlcuddidl

RUN opam pin add dice git+https://github.com/SHoltzen/dice.git#master

