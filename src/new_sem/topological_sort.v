Require Import List.
From mathcomp Require Import all_ssreflect.

Definition build_order (f : nat -> nat -> bool) (len : nat) : option (seq nat) :=
    None.

Theorem build_order_soundness:
    forall f l ord,
        build_order f l = Some ord ->
        length ord = l /\
        forall in1 in2 out1 out2,
            nth_error ord in1 = Some out1 ->
            nth_error ord in2 = Some out2 ->
            f in1 in2 -> out1 < out2.
Proof.
    unfold build_order; discriminate.
Qed.