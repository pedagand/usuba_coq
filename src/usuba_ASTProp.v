From Usuba Require Import ident usuba_AST.

Lemma ident_beq_refl:
    forall x, ident_beq x x = true.
Proof.
    intro x; rewrite ident_beq_eq; reflexivity.
Qed.

Lemma ident_beq_sym:
    forall x y, ident_beq x y = ident_beq y x.
Proof.
    intros x y.
    case_eq (ident_beq y x); [> idtac | do 2 rewrite <-Bool.not_true_iff_false ].
    all: do 2 rewrite ident_beq_eq; auto.
Qed.

Lemma ident_eq_dec:
    forall x y : ident, { x = y } + { x <> y}.
Proof.
    intros x y; case_eq (ident_beq x y); intro H; [> left | right].
    2: rewrite <- Bool.not_true_iff_false in H.
    all: rewrite ident_beq_eq in H; assumption.
Qed.
