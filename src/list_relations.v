Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST usuba_ASTProp arch.

(* Relations between two lists *)

Inductive list_rel {A B} (R : A -> B -> Prop) : list A -> list B -> Prop :=
    | LRnil : list_rel R nil nil
    | LRcons : forall h1 h2 t1 t2,
        R h1 h2 -> list_rel R t1 t2 -> list_rel R (h1 :: t1) (h2 :: t2)
.

Inductive list_rel_top {A B} (R : A -> B -> Prop) : list A -> list B -> Prop :=
    | LRTnilL : forall l, list_rel_top R nil l
    | LRTnilR : forall l, list_rel_top R l nil
    | LRTcons : forall h1 h2 t1 t2,
        R h1 h2 -> list_rel_top R t1 t2 -> list_rel_top R (h1 :: t1) (h2 :: t2)
.

Lemma list_rel_length {A B} (R : A -> B -> Prop):
    forall l1 l2,
        list_rel R l1 l2 -> length l1 = length l2.
Proof.
    move=> l1 l2 lr; induction lr as [|h1 h2 t1 t2 H_hd H_tl HRec]; simpl; auto.
Qed.

Lemma list_rel_append {A B} (R : A -> B -> Prop):
    forall l1 l2 l3 l4,
        list_rel R (l1 ++ l3) (l2 ++ l4) /\ length l1 = length l2 <->
        list_rel R l1 l2 /\ list_rel R l3 l4.
Proof.
    move=> l1; induction l1 as [|h1 t1 HRec]; simpl.
    {
        move=> [|h2 t2] l3 l4; simpl; split.
        by move=> [H _]; split; [> constructor | assumption].
        by move=> [_ H]; split; [> assumption | reflexivity].
        by move=> [_ H]; discriminate.
        by move=> [H _]; inversion H.
    }
    {
        move=> [|h2 t2] l3 l4; simpl; split.
        by move=> [_ H]; discriminate.
        by move=> [H _]; inversion H.
        {
            move=> [H1 H2]; inversion H1.
            destruct (HRec t2 l3 l4) as [imp_1 _].
            move: imp_1.
            impl_tac; auto.
            move=> [HRec' HRec'2].
            split; trivial.
            constructor; assumption.
        }
        {
            move=> [H1 H2]; inversion H1.
            destruct (HRec t2 l3 l4) as [_ imp_2].
            move: imp_2.
            impl_tac; auto.
            move=> [HRec' ->].
            split; trivial.
            constructor; assumption.
        }
    }
Qed.

Lemma list_rel_last {A B} (R : A -> B -> Prop):
    forall l1 l2 i1 i2,
        list_rel R (l1 ++ [:: i1]) (l2 ++ [:: i2]) <->
        list_rel R l1 l2 /\ R i1 i2.
Proof.
    move=> l1 l2 i1 i2; split.
    {
        move=> l_rel.
        destruct (list_rel_append R l1 l2 [:: i1] [:: i2]) as [imp_1 _].
        move: imp_1.
        impl_tac.
        {
            split; trivial.
            apply list_rel_length in l_rel.
            do 2 rewrite app_length in l_rel.
            simpl in l_rel.
            do 2 rewrite Nat.add_1_r in l_rel.
            inversion l_rel; trivial.
        }
        {
            move=> [H H'].
            inversion H'.
            split; trivial.
        }
    }
    {
        move=> [l_rel last_rel].
        destruct (list_rel_append R l1 l2 [:: i1] [:: i2]) as [_ imp_2].
        move: imp_2.
        impl_tac.
        {
            split; trivial.
            by constructor; [> assumption | constructor].
        }
        {
            move=> [H _]; assumption.
        }
    }
Qed.

Lemma list_rel_top_eq {A}:
    forall (l1 l2 l3 : seq A),
        list_rel_top eq (l1 ++ l2) l3 -> list_rel_top eq l1 l3.
Proof.
    move=> l1 l2; induction l1 as [|h1 t1 HRec]; simpl.
    by intros; constructor.
    move=> [|h3 t3] lrel; constructor.
    all: inversion lrel; auto.
Qed.

Lemma list_rel_trans {A} {R : A -> A -> Prop} :
    (forall x y z, R x y -> R y z -> R x z) ->
    forall l1 l2 l3, list_rel R l1 l2 -> list_rel R l2 l3 -> list_rel R l1 l3.
Proof.
    move=> trans l1 l2 l3 LR; move: l3; induction LR.
    all: move=> l3 LR2; inversion LR2 as [|h2' h3 t2' t3 R_hd R_tl]; constructor; auto.
    refine (trans _ _ _ _ R_hd); trivial.
Qed.

Lemma list_rel_top_soundness {A B : Type} {R : A -> B -> Prop}:
    forall l1 l2,
        list_rel_top R l1 l2 ->
            exists l1a l1b l2a l2b,
                l1 = l1a ++ l1b /\ l2 = l2a ++ l2b /\
                list_rel R l1a l2a /\ (l1b = nil \/ l2b = nil).
Proof.
    move=> l1 l2 rel; induction rel as [t2|t1|h1 h2 t1 t2 rel_hd rel_tl [l1a [l1b [l2a [l2b [-> [-> [rel empty]]]]]]]].
    {
        do 3 exists nil; exists t2; simpl.
        repeat split; auto.
        by constructor.
    }
    {
        exists nil; eexists; do 2 exists nil; simpl.
        repeat split; auto.
        by constructor.
    }
    {
        exists (h1 :: l1a); exists l1b; exists (h2 :: l2a); exists l2b.
        repeat split; auto.
        by constructor.
    }
Qed.

Lemma list_rel_eq_is_eq {A}:
    forall l1 l2,
        list_rel (@eq A) l1 l2 <-> l1 = l2.
Proof.
    move=> l1; induction l1 as [|h1 t1 HRec].
    all: move=> [|h2 t2]; split.
    1-7: move=> H; inversion H; trivial.
    by constructor.
    by f_equal; [> trivial | rewrite <-HRec; trivial ].
    by move=> H; constructor; [> idtac | rewrite HRec ]; inversion H; reflexivity.
Qed.

Lemma list_rel_top_same_length {A B} {R : A -> B -> Prop}:
    forall l1 l2, list_rel_top R l1 l2 -> length l1 = length l2 -> list_rel R l1 l2.
Proof.
    move=> l1 l2 lrel; induction lrel as [l|l|h1 h2 t1 t2 r_hd r_tl HRec].
    1,2: destruct l; simpl.
    1,3: by intro; constructor.
    all: move=> H; inversion H; constructor; auto.
Qed.

Lemma list_rel_imp_In_l {A B} {R : A -> B -> Prop}:
    forall l1 l2, list_rel R l1 l2 ->
        forall elt, List.In elt l1 -> exists elt', List.In elt' l2 /\ R elt elt'.
Proof.
    move=> l1 l2 lr.
    induction lr as [|h1 h2 t1 t2 H_hd H_tl HRec]; simpl.
    by idtac.
    move=> elt [HEq|LIn].
    by destruct HEq; eexists; split; [> left; reflexivity | exact H_hd].
    destruct (HRec _ LIn) as [elt' [LIn' Hrel]].
    exists elt'; auto.
Qed.

Lemma list_rel_imp_In_r {A B} {R : A -> B -> Prop}:
    forall l1 l2, list_rel R l1 l2 ->
        forall elt', List.In elt' l2 -> exists elt, List.In elt l1 /\ R elt elt'.
Proof.
    move=> l1 l2 lr.
    induction lr as [|h1 h2 t1 t2 H_hd H_tl HRec]; simpl.
    by idtac.
    move=> elt [HEq|LIn].
    by destruct HEq; eexists; split; [> left; reflexivity | exact H_hd].
    destruct (HRec _ LIn) as [elt' [LIn' Hrel]].
    exists elt'; auto.
Qed.

Lemma list_rel_untop {A B} {R : A -> B -> Prop}:
    forall l1 l2 l3 l4, list_rel R l1 l2 -> list_rel_top R l3 l4 -> list_rel_top R (l1 ++ l3) (l2 ++ l4).
Proof.
    move=> l1 l2 l3 l4 lrel; move: l3 l4.
    induction lrel as [|h1 h2 t1 t2 r_hd r_tl HRec]; simpl.
    by trivial.
    intros; constructor; auto.
Qed.
