#!/bin/sh

make -f CoqMakefile
rm -f semantic_aes.mli semantic_aes_subst.mli semantic_aes_topo.mli tmp_test.*

echo "Testing Evaluation semantic"
echo "open Semantic_aes" > tmp_test.ml
cat test.ml >> tmp_test.ml
ocamlfind ocamlopt -o a.out -linkpkg -package zarith semantic_aes.ml tmp_test.ml
./a.out
rm a.out semantic_aes.cm* semantic_aes.o tmp_test.*

echo "Testing Fixpoint semantic"
echo "open Semantic_aes_subst" > tmp_test.ml
cat test.ml >> tmp_test.ml
ocamlfind ocamlopt -o a.out -linkpkg -package zarith semantic_aes_subst.ml tmp_test.ml
./a.out
rm a.out semantic_aes_subst.cm* semantic_aes_subst.o tmp_test.*

echo "Testing Topological semantic"
echo "open Semantic_aes_topo" > tmp_test.ml
cat test.ml >> tmp_test.ml
ocamlfind ocamlopt -o a.out -linkpkg -package zarith semantic_aes_topo.ml tmp_test.ml
./a.out
rm a.out semantic_aes_topo.cm* semantic_aes_topo.o tmp_test.*
