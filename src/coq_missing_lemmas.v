Require Import String.
Require Import List.
Require Import PeanoNat.
From mathcomp Require Import all_ssreflect.

(* length and app *)

Lemma length_app {A : Type}:
    forall l1 l2 : list A,
        length (l1 ++ l2) = length l1 + length l2.
Proof.
    move=> l1 l2; induction l1 as [|hd l1 HRec]; simpl.
    {
        rewrite add0n; trivial.
    }
    {
        rewrite addSn.
        rewrite HRec; reflexivity.
    }
Qed.

Lemma length_app_eq {A : Type}:
    forall l1 l2 : list A,
    forall i1 i2,
        length l1 = i1 -> length (l1 ++ l2) = i1 + i2 -> length l2 = i2.
Proof.
    move=> l1 l2; induction l1 as [|hd l1 HRec]; simpl.
    all: move=> i1 i2 <-.
    {
        rewrite add0n; trivial.
    }
    {
        rewrite addSn.
        move=> HEq; inversion HEq.
        refine (HRec _ _ _ _).
        + reflexivity.
        + assumption.
    }
Qed.

Lemma case_last {A : Type}: forall l : list A, {l = nil} + {exists l' last, l = l' ++ last::nil}.
Proof.
    induction l as [|hd tl HRec]; simpl; auto.
    right.
    destruct HRec as [->|[l' [last' ->]]].
    {
        exists nil; exists hd; simpl; reflexivity.
    }
    {
        exists (hd::l'); exists last'; simpl; reflexivity.
    }
Qed.


Lemma Forall_length_1_concat {A : Type}:
    forall l : list (list A),
        Forall (fun l2 => length l2 = 1) l -> length (concat l) = length l.
Proof.
    move=> l; induction l as [|hd l HRec]; simpl; trivial.
    move=> HForall.
    rewrite length_app.
    rewrite HRec.
    + apply Forall_inv in HForall; rewrite HForall; rewrite add1n; reflexivity.
    + apply Forall_inv_tail in HForall; assumption.
Qed.

Lemma leb_add_1_l:
    forall n, n + 1 <=? n  = false.
Proof.
    induction n; simpl; auto.
Qed.

Lemma leq_Cases:
    forall l1 l2,
        l1 <= l2 -> l1 = l2 \/ l1 < l2.
Proof.
    move=> l1; induction l1 as [|l1 HRec].
    all: move=> [|l2]; simpl; auto.
    rewrite ltnS.
    move=> H; destruct (HRec _ H) as [->| H']; auto.
Qed.

Lemma String_append_length:
    forall (s1 s2 : string),
        String.length (s1 ++ s2)%string = String.length s1 + String.length s2.
Proof.
    intros s1 s2; induction s1; simpl.
    + reflexivity.
    + rewrite IHs1; reflexivity.
Qed.

(* list map is ss_reflect map *)
Theorem list_map_seq_map {A B : Type} (f : A -> B):
    forall l, List.map f l = [seq f i | i <- l].
Proof.
    move=> l; induction l as [|hd tl HRec]; simpl; trivial.
Qed.

Lemma app_inj {A : Type}:
    forall l1 l2 l3 : list A,
        l1 ++ l2 = l1 ++ l3 -> l2 = l3.
Proof.
    move=> l1 l2 l3; induction l1 as [|hd tl HRec]; simpl; trivial.
    move=> H; apply HRec.
    inversion H; reflexivity.
Qed.
