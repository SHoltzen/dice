FROM ocaml/opam2

WORKDIR dice

ADD dice.opam .

RUN opam pin add -yn dice . && \
    opam depext dice

RUN opam install dice



