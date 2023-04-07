From Usuba Require Import usuba_AST.

Lemma ident_beq_refl:
    forall x, ident_beq x x = true.
Proof.
    intro x; rewrite ident_beq_eq; reflexivity.
Qed.

Lemma ident_eq_dec:
    forall x y : ident, { x = y } + { x <> y}.
Proof.
    intros x y; case_eq (ident_beq x y); intro H; [> left | right].
    2: rewrite <- Bool.not_true_iff_false in H.
    all: rewrite ident_beq_eq in H; assumption.
Qed.
