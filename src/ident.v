From Coq Require Import FMapAVL.
From Coq Require Import String.
Require Import OrderedType.
Require Import Coq.Structures.OrdersEx.

Inductive ident :=
    | Id_s : string -> ident
    | Num : nat -> ident.
Scheme Equality for ident.

Lemma ident_beq_eq: forall x y, ident_beq x y = true <-> x = y.
Proof.
    intros; split; intro.
    + apply internal_ident_dec_bl; assumption.
    + apply internal_ident_dec_lb; assumption.
Qed.

Module Ident_as_OT_map <: OrderedType.
    Definition t := ident.
    (* Include HasUsualEq <+ UsualIsEq. *)
    Definition eq := @eq t.
    Definition eqb := ident_beq.
    Definition eqb_eq := ident_beq_eq.
    Definition eq_dec := ident_eq_dec.
    (* Include HasEqBool2Dec. *)

    Definition eq_refl := @eq_refl t.
    Definition eq_sym := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    Definition cmp (a b : ident)
        := match a, b with
            | Id_s a, Id_s b => String_as_OT.compare a b
            | Id_s _, Num _ => Lt
            | Num _, Id_s _ => Gt
            | Num a, Num b => Nat.compare a b
        end.

    Definition lt (a b : ident) := cmp a b = Lt.

    #[global]
    Instance lt_compat : Proper (eq==>eq==>iff) lt.
    Proof.
        intros x x' H; destruct H.
        intros y y' H; destruct H.
        split; trivial.
    Qed.

    Lemma compare : forall x y, Compare lt eq x y.
    Proof.
        intros x y.
        pose (p := cmp x y).
        destruct x as [s1|n1]; destruct y as [s2|n2]; simpl in *.
        1: pose (p' := String_as_OT.compare_spec s1 s2); generalize p'; clear p'; fold p.
        4: pose (p' := Nat_as_OT.compare_spec n1 n2); generalize p'; clear p'; fold p.
        all: case_eq p; unfold p; clear p.
        4,6,7,8: discriminate.
        all: intro H.
        1-3: intro H2; [> constructor 2 | constructor 1 | constructor 3].
        6-8: intro H2; [> constructor 2 | constructor 1 | constructor 3].
        4-5: [> constructor 1 | constructor 3].
        all: unfold lt, eq; simpl; auto.
        1,3: f_equal.
        all: inversion H2; auto.
        rewrite PeanoNat.Nat.compare_lt_iff; assumption.
    Qed.

    #[global]
    Instance lt_strorder : StrictOrder lt.
    Proof.
        destruct (String_as_OT.lt_strorder).
        destruct (Nat_as_OT.lt_strorder).
        split.
        {
            unfold Irreflexive, Reflexive, complement, lt in *.
            intro x; destruct x as [s|n]; simpl.
            + apply StrictOrder_Irreflexive.
            + rewrite PeanoNat.Nat.compare_lt_iff; apply StrictOrder_Irreflexive0.
        }
        {
            unfold Transitive, lt in *.
            intro x; destruct x as [s1|n1]; simpl.
            all: intro x; destruct x as [s2|n2]; simpl.
            all: intro x; destruct x as [s3|n3]; simpl; trivial.
            + apply StrictOrder_Transitive.
            + discriminate.
            + discriminate.
            + do 3 rewrite PeanoNat.Nat.compare_lt_iff;
                apply StrictOrder_Transitive0.
        }
    Qed.

    Definition lt_trans := StrictOrder_Transitive.
    Lemma lt_not_eq : forall x y, lt x y -> x <> y.
    Proof.
        pose (p := StrictOrder_Irreflexive).
        unfold Irreflexive, Reflexive, complement in *.
        intros x y Hlt HEq; destruct HEq; apply p in Hlt.
        assumption.
    Qed.

End Ident_as_OT_map.

Module imap := Make Ident_as_OT_map.

From Coq Require Import MSets.

Module Ident_as_OT_set <: UsualOrderedType.
    Definition t := ident.
    Include HasUsualEq <+ UsualIsEq.
    Definition eqb := ident_beq.
    Definition eqb_eq := ident_beq_eq.
    Include HasEqBool2Dec.

    Definition compare (a b : ident)
        := match a, b with
            | Id_s a, Id_s b => String_as_OT.compare a b
            | Id_s _, Num _ => Lt
            | Num _, Id_s _ => Gt
            | Num a, Num b => Nat.compare a b
        end.

    Definition lt (a b : ident) := compare a b = Lt.

#[global]
    Instance lt_compat : Proper (eq==>eq==>iff) lt.
    Proof.
        intros x x' H; destruct H.
        intros y y' H; destruct H.
        split; trivial.
    Qed.

    Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
    Proof.
        intros x y.
        unfold CompSpec.
        destruct x as [s1|n1]; destruct y as [s2|n2]; simpl.
        all: unfold lt, eq; simpl.
        2,3: constructor; reflexivity.
        {
            pose (p := String_as_OT.compare_spec s1 s2).
            unfold CompSpec, String_as_OT.eq, String_as_OT.lt in p.
            generalize p; clear p; intro p.
            destruct (String_as_OT.compare s1 s2); inversion p; constructor; auto.
            f_equal; assumption.
        }
        {
            pose (p := Nat_as_OT.compare_spec n1 n2).
            unfold CompSpec, Nat_as_OT.eq, Nat_as_OT.lt in p.
            generalize p; clear p; intro p.
            destruct (Nat_as_OT.compare n1 n2); inversion p; constructor; auto.
            rewrite PeanoNat.Nat.compare_lt_iff; assumption.
        }
    Qed.

#[global]
    Instance lt_strorder : StrictOrder lt.
    Proof.
        destruct (String_as_OT.lt_strorder).
        destruct (Nat_as_OT.lt_strorder).
        split.
        {
            unfold Irreflexive, Reflexive, complement, lt in *.
            intro x; destruct x as [s|n]; simpl.
            + apply StrictOrder_Irreflexive.
            + rewrite PeanoNat.Nat.compare_lt_iff; apply StrictOrder_Irreflexive0.
        }
        {
            unfold Transitive, lt in *.
            intro x; destruct x as [s1|n1]; simpl.
            all: intro x; destruct x as [s2|n2]; simpl.
            all: intro x; destruct x as [s3|n3]; simpl; trivial.
            + apply StrictOrder_Transitive.
            + discriminate.
            + discriminate.
            + do 3 rewrite PeanoNat.Nat.compare_lt_iff;
                apply StrictOrder_Transitive0.
        }
    Qed.

End Ident_as_OT_set.

Module iset := Make Ident_as_OT_set.