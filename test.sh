#!/bin/sh

make -f CoqMakefile
cat semantic_aes.ml > tmp.ml
cat test.ml >> tmp.ml
ocaml tmp.ml
rm tmp.ml
