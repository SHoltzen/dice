PKGNAME = dice

build:
	ocamlbuild -use-ocamlfind src/Dice.native
clean:
	ocamlbuild -clean
install:
	ocamlbuild -use-ocamlfind src/Dice.native
bench:
	ocamlbuild -use-ocamlfind src/Run_bench.native
test:
	ocamlbuild -use-ocamlfind src/Test.native

