build:
	ocamlbuild -use-ocamlfind -use-menhir  src/Dice.native
clean:
	ocamlbuild -clean
bench:
	ocamlbuild -use-ocamlfind -use-menhir src/Run_bench.native
test:
	ocamlbuild -use-ocamlfind -use-menhir src/Test.native
top:
	ocamlbuild -classic-display -no-links -use-ocamlfind -tag thread -pkg threads,utop myutop.top

