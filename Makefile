build:
	ocamlbuild -use-ocamlfind -use-menhir src/Main.native
clean:
	ocamlbuild -clean
test:
	ocamlbuild -cflag -g -use-ocamlfind src/Test.p.native
top:
	ocamlbuild -classic-display -no-links -use-ocamlfind -tag thread -pkg threads,utop myutop.top

.PHONY: main test clean
