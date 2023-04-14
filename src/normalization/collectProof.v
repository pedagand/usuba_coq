From Usuba Require Import ident usuba_AST collect usuba_sem equiv_rel.
(* From Coq Require Import MSets MSets.MSetToFiniteSet MSets.MSetFacts. *)
(* Require Import Coq.Structures.OrdersEx. *)
From mathcomp Require Import all_ssreflect.
Require Import Coq.Sets.Ensembles.

Lemma iset_empty_soudness:
    forall elt : iset.elt,
    iset.In elt iset.empty <-> In ident (Empty_set ident) elt.
Proof.
    move=> elt.
        pose (Hempty := iset.empty_spec).
        unfold iset.Empty in Hempty.
        specialize Hempty with elt.
        split.
        + move=> H; exfalso; auto.
        + move=> [].
Qed.

Lemma collect_aexpr_soundness:
    forall ae elt,
        iset.In elt (collect_aexpr ae) <-> In ident (aexpr_freevars ae) elt.
Proof.
    move=> ae; induction ae as [| |op ae1 HRec1 ae2 HRec2]; simpl.
    {
        exact iset_empty_soudness.
    }
    {
        move=> elt; rewrite iset.singleton_spec; split.
        + move=> ->; constructor.
        + move=> []; reflexivity.
    }
    {
        move=> elt; rewrite iset.union_spec.
        rewrite HRec1; rewrite HRec2; split.
        + move=> []; constructor; assumption.
        + move=> []; auto.
    }
Qed.

Lemma collect_aexprl_soundness:
    forall ael elt,
        iset.In elt (collect_aexprl ael) <-> In ident (aexprl_freevars ael) elt.
Proof.
    move=> ael; induction ael as [|hd tl HRec]; simpl; move=> elt.
    {
        exact (iset_empty_soudness _).
    }
    {
        rewrite iset.union_spec.
        rewrite collect_aexpr_soundness; rewrite HRec.
        split; move=> []; auto; move=> HIn; constructor; assumption.
    }
Qed.

Lemma collect_var_soundness:
    forall var elt,
        iset.In elt (collect_var var) <-> In ident (var_freevars var) elt.
Proof.
    move=> var; induction var as [|v HRec ae|v HRec ae1 ae2|v HRec aeL].
    all: simpl; move=> elt.
    {
        rewrite iset.singleton_spec; split.
        + move=> ->; constructor.
        + move=> []; reflexivity.
    }
    {
        rewrite iset.union_spec; rewrite HRec; rewrite collect_aexpr_soundness; split.
        + move=> []; constructor; assumption.
        + move=> []; auto.
    }
    {
        do 2 rewrite iset.union_spec; rewrite HRec; do 2 rewrite collect_aexpr_soundness; split.
        + move => [|[]].
            - constructor; assumption.
            - do 2 constructor; assumption.
            - do 2 constructor; assumption.
        + move => [|x []]; auto.
    }
    {
        rewrite iset.union_spec; rewrite HRec; rewrite collect_aexprl_soundness; split.
        + move=> []; constructor; assumption.
        + move=> []; auto.
    }
Qed.

Lemma collect_varl_soundness:
    forall varl elt,
        iset.In elt (collect_varl varl) <-> In ident (varl_freevars varl) elt.
Proof.
    move=> varl; induction varl as [|hd tl HRec]; simpl; move=> elt.
    {
        pose (Hempty := iset.empty_spec).
        unfold iset.Empty in Hempty.
        specialize Hempty with elt.
        split.
        + move=> H; exfalso; auto.
        + move=> [].
    }
    {
        rewrite iset.union_spec; rewrite collect_var_soundness.
        rewrite HRec; split.
        + move=> []; constructor; assumption.
        + move=> []; auto.
    }
Qed.

Lemma collect_expr_soundness:
    forall e elt,
        iset.In elt (collect_expr e) <-> In ident (expr_freevars e) elt.
Proof.
    move=> e.
    refine (expr_find (fun e => _) (fun exprL => _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ e); simpl; auto; clear e.
    {
        intros; exact (iset_empty_soudness _).
    }
    {
        intros; exact (collect_var_soundness _ _).
    }
    {
        move=> e0 HRec elt; exact (HRec elt).
    }
    {
        move=> _ e1 HRec1 e2 HRec2 elt.
        rewrite iset.union_spec; rewrite HRec1; rewrite HRec2.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        move=> _ e1 HRec1 e2 HRec2 elt.
        rewrite iset.union_spec; rewrite HRec1; rewrite HRec2.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        move=> _ e1 HRec1 ae elt.
        rewrite iset.union_spec; rewrite HRec1; rewrite collect_aexpr_soundness.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        intros; exact (collect_var_soundness _ _).
    }
    {
        move=> e HRec ae elt; rewrite iset.union_spec.
        rewrite HRec; rewrite collect_aexpr_soundness.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        move=> e1 HRec1 e2 HRec2 typ elt.
        rewrite iset.union_spec; rewrite HRec1; rewrite HRec2.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        move=> i el HRec elt; rewrite iset.union_spec.
        rewrite iset.singleton_spec; rewrite HRec.
        split; move=> []; auto.
        + move=> ->; do 2 constructor.
        + intro; constructor; assumption.
        + move=> x []; left; reflexivity.
    }
    {
        move=> i ae el HRec elt; do 2 rewrite iset.union_spec.
        rewrite iset.singleton_spec; rewrite collect_aexpr_soundness; rewrite HRec.
        split.
        + move=> [->|[HIn|HIn]]; do 2 constructor; assumption.
        + move=> [x []| x []]; auto.
    }
    {
        simpl; exact iset_empty_soudness.
    }
    {
        move=> e HRec el HRecl elt; simpl.
        rewrite iset.union_spec; rewrite HRec; rewrite HRecl.
        split; move=> []; auto; intro; constructor; assumption.
    }
Qed.

Lemma collect_deqs_soundness_lemma:
    forall deqs elt,
        iset.In elt (collect_deqs (list_deq_of_deqL deqs)) <-> In ident (deqs_vars (list_deq_of_deqL deqs)) elt.
Proof.
    move=> deqs elt; induction deqs as [|v e b tl HRec|i ae1 ae2 body HRecBody opt tl HRecTL]; simpl.
    {
        exact (iset_empty_soudness _).
    }
    {
        do 2 rewrite iset.union_spec; rewrite HRec.
        rewrite collect_varl_soundness; rewrite collect_expr_soundness.
        split; move=> []; auto.
        + move=> []; do 2 constructor; assumption.
        + intro; constructor; assumption.
        + move=> x []; auto.
    }
    {
        rewrite iset.union_spec.
        rewrite iset.add_spec; do 2 rewrite iset.union_spec.
        rewrite HRecBody; rewrite HRecTL.
        do 2 rewrite collect_aexpr_soundness; split.
        + move=> [[|[[]|]]|].
            - by move=> ->; do 3 constructor.
            - intro; do 3 constructor; assumption.
            - intro; do 4 constructor; assumption.
            - intro; do 4 constructor; assumption.
            - intro; do 1 constructor; assumption.
        + move=> [x [x' []|x' [|x'2 []]]|]; auto.
    }
Qed.

Lemma collect_bounddeqs_soundness_lemma:
    forall deqs elt,
        iset.In elt (collect_bounddeqs (list_deq_of_deqL deqs)) <-> In ident (deqs_boundvars (list_deq_of_deqL deqs)) elt.
Proof.
    move=> deqs elt; induction deqs as [|v e b tl HRec|i ae1 ae2 body HRecBody opt tl HRecTL]; simpl.
    {
        exact (iset_empty_soudness _).
    }
    {
        rewrite iset.union_spec; rewrite HRec.
        rewrite collect_varl_soundness.
        split; move=> []; auto.
        all: intro; constructor; assumption.
    }
    {
        rewrite iset.union_spec.
        rewrite iset.add_spec.
        rewrite HRecBody; rewrite HRecTL; split.
        + move=> [[]|].
            - by move=> ->; do 2 constructor.
            - intro; do 2 constructor; assumption.
            - intro; do 1 constructor; assumption.
        + move=> [x [x' []|]|]; auto.
    }
Qed.

Lemma collect_deqs_soundness:
    forall deqs elt,
        iset.In elt (collect_deqs deqs) <-> In ident (deqs_vars deqs) elt.
Proof.
    move=> deqs elt.
    pose (HEq := collect_deqs_soundness_lemma (deqL_of_list_deq deqs) elt); move: HEq.
    rewrite deqL_is_list_deq; auto.
Qed.
