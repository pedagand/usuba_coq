Require Import List.
Require Import ZArith.
From Usuba Require Import usuba_AST collect clean
    usuba_sem arch aes ace_bitslice.
Require Extraction.
Require Import ExtrOcamlNativeString ExtrOcamlZBigInt.

Extraction Language OCaml.


Extract Inductive bool => bool [ true false ].
Extract Inductive list => "list" [ "[]" "(::)" ]. 
Extraction "usuba" clean_prog.

Extraction "semantic_aes" prog_sem prog_aes prog_ace_bs default_arch.
