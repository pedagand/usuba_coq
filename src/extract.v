Require Import List.
Require Import ZArith.
From Usuba Require Import usuba_AST.
Require Extraction.
Require Import ExtrOcamlNativeString.

Extraction Language OCaml.


Extract Inductive bool => bool [ true false ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction "usuba" prog.
