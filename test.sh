#!/bin/sh

make -f CoqMakefile
rm -f semantic_aes.mli
ocamlfind ocamlopt -o a.out -linkpkg -package zarith semantic_aes.ml test.ml
./a.out
rm a.out semantic_aes.cm* semantic_aes.o
