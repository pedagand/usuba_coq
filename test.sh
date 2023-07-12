#!/bin/sh

make -f CoqMakefile
rm -f semantic_aes.mli semantic_aes_subst.mli
ocamlfind ocamlopt -o a.out -linkpkg -package zarith semantic_aes.ml test.ml
./a.out
rm a.out semantic_aes.cm* semantic_aes.o
ocamlfind ocamlopt -o a.out -linkpkg -package zarith semantic_aes_subst.ml test2.ml
./a.out
rm a.out semantic_aes_subst.cm* semantic_aes_subst.o
