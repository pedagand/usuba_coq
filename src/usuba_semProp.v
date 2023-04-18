Require Import Lia.
Require Import List.
Require Import PeanoNat.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST usuba_sem coq_missing_lemmas arch.

(* Properties on prod_list *)

Fixpoint simpl_form (form : list nat) : list nat :=
    match form with
    | nil => nil
    | 1::tl => simpl_form tl
    | hd::tl => hd::simpl_form tl
    end.

Lemma simpl_form_preserve_prod:
    forall form, prod_list form = prod_list (simpl_form form).
Proof.
    move=> form; induction form as [|[|[|hd'']] tl HRec]; simpl; trivial.
    + rewrite <- HRec; clear HRec.
        unfold muln, muln_rec; rewrite Nat.mul_1_l; reflexivity.
    + rewrite <- HRec; reflexivity.
Qed.

Lemma prod_list_append:
    forall l1 l2,
        prod_list (l1 ++ l2)%list = prod_list l1 * prod_list l2.
Proof.
    move=> l1; induction l1 as [|hd l1 HRec]; simpl; move=> l2.
    {
        unfold muln, muln_rec; rewrite Nat.mul_1_l; reflexivity.
    }
    {
        rewrite HRec.
        unfold muln, muln_rec; rewrite Nat.mul_assoc; reflexivity.
    }
Qed.

(* Relation between find_val and find_const *)

Lemma find_val_imp_find_const:
    forall x ctxt1 ctxt2,
        find_val ctxt1 x = find_val ctxt2 x -> find_const ctxt1 x = find_const ctxt2 x.
Proof.
    move=> x ctxt1.
    induction ctxt1 as [|[n1 v1] ctxt1 HRec1]; simpl.
    {
        move=> ctxt2; induction ctxt2 as [|[n v] tl HRec]; simpl; trivial.
        case (ident_beq x n).
        + discriminate.
        + assumption.
    }
    {
        move=> ctxt2.
        case (ident_beq x n1); auto.
        induction ctxt2 as [|[n2 v2] ctxt2 HRec2]; simpl.
        + discriminate.
        + case (ident_beq x n2).
            - move=> HEq; inversion HEq; reflexivity.
            - assumption.
    }
Qed.

(* linearize_list_value properties *)

Lemma map_CoIL_is_lin {A : Type}:
    forall l, @linearize_list_value A [seq CoIL i | i <- l] nil = [seq CoIL i | i <- l].
Proof.
    move=> l; induction l as [|hd tl HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Theorem linearize_map_CoIL {A : Type} :
    forall l1 l2, @linearize_list_value A (List.map CoIL l1) l2 = (List.map CoIL l1) ++ l2.
Proof.
    move=> l1 l2; induction l1 as [|hd l1 HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Theorem eval_var_linearize_fixpoint:
    forall ctxt v acc l, eval_var v ctxt acc = Some l -> linearize_list_value l nil = l.
Proof.
    move=> ctxt; induction v as [v|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl; move=> acc l.
    {
        destruct (find_val ctxt v) as [[cst|dir iL [dim|]]|].
        3-4: discriminate.
        {
            case (get_access [:: Some cst] acc nil); case acc.
            + move=> l' HEq; inversion HEq; simpl.
                clear; induction l' as [|hd tl HRec]; simpl; trivial.
                f_equal; assumption.
            + move=> _ _ l' HEq; inversion HEq; apply map_CoIL_is_lin.
            + discriminate.
            + discriminate.
        }
        {
            case (get_access iL acc dim); case acc.
            + move=> l' HEq; inversion HEq; simpl; reflexivity.
            + move=> _ _ l' HEq; inversion HEq; simpl; reflexivity.
            + discriminate.
            + discriminate.
        }
    }
    {
        case (eval_arith_expr ctxt ae).
        2: by discriminate.
        intros n H; exact (HRec _ _ H).
    }
    {
        case (eval_arith_expr ctxt ae1).
        2: by discriminate.
        case (eval_arith_expr ctxt ae2).
        2: by discriminate.
        intros n1 n2 H; exact (HRec _ _ H).
    }
    {
        match goal with
        | |- match ?f with Some _ => _ | None => _ end = _ -> _ => case f
        end.
        2: by discriminate.
        intros n H; exact (HRec _ _ H).
    }
Qed.

(* take n property *)

Lemma take_n_sum {A : Type} :
    forall l l2: list A, forall n, length l = n -> take_n n (l ++ l2) = Some (l, l2).
Proof.
    move=> l l2; induction l as [|hd tl HRec]; simpl.
    {
        move=> n <-; simpl; reflexivity.
    }
    {
        move=> [|n] HEq; simpl.
        by discriminate.
        rewrite HRec; trivial.
        inversion HEq; reflexivity.
    }
Qed.

Lemma take_n_all {A : Type} :
    forall l : list A, forall n, length l = n -> take_n n l = Some (l, nil).
Proof.
    move=> l; induction l as [|hd tl HRec]; simpl.
    {
        move=> n <-; simpl; reflexivity.
    }
    {
        move=> [|n] HEq; simpl.
        by discriminate.
        rewrite HRec; trivial.
        inversion HEq; reflexivity.
    }
Qed.

Lemma take_n_soundness { A : Type} :
    forall i l,
        i <= length l ->
        exists l1 l2, @take_n A i l = Some (l1, l2) /\ l = l1 ++ l2 /\ length l1 = i.
Proof.
    move=> i; induction i as [|i HRec]; simpl.
    {
        move=> l _.
        exists nil; exists l; auto.
    }
    {
        move=> [|hd tl]; simpl.
        {
            discriminate.
        }
        specialize HRec with tl.
        move=> Hlt; move: HRec.
        impl_tac.
        {
            apply ltnSE; assumption.
        }
        move=> [l1 [l2 [TakeEq [EqAppend LengthEq]]]].
        rewrite TakeEq.
        exists (hd::l1); exists l2.
        simpl.
        rewrite LengthEq.
        repeat split; trivial.
        rewrite EqAppend.
        simpl; reflexivity.
    }
Qed.

Lemma take_n_soundness2 { A : Type} :
    forall i l,
        i <= length l ->
        exists l1 l2, @take_n (option A) i (List.map Some l) = Some (List.map Some l1, map Some l2) /\ l = l1 ++ l2 /\ length l1 = i.
Proof.
    move=> i; induction i as [|i HRec]; simpl.
    {
        move=> l _.
        exists nil; exists l; auto.
    }
    {
        move=> [|hd tl]; simpl.
        {
            discriminate.
        }
        specialize HRec with tl.
        move=> Hlt; move: HRec.
        impl_tac.
        {
            apply ltnSE; assumption.
        }
        move=> [l1 [l2 [TakeEq [EqAppend LengthEq]]]].
        rewrite TakeEq.
        exists (hd::l1); exists l2.
        simpl.
        rewrite LengthEq.
        repeat split; trivial.
        rewrite EqAppend.
        simpl; reflexivity.
    }
Qed.

Lemma try_take_n_all { A : Type} :
    forall i l,
        i = length l ->
        @try_take_n A i l = (l, IoLR A nil).
Proof.
    move=> i; induction i as [|i HRec]; simpl.
    {
        move=> []; simpl; trivial.
        by discriminate.
    }
    {
        move=> [|hd tl]; simpl.
        by discriminate.
        specialize HRec with tl.
        move=> HEq; move: HRec.
        impl_tac.
        + inversion HEq; reflexivity.
        + move=> ->; reflexivity.
    }
Qed.

Lemma try_take_n_soundness { A : Type} :
    forall i l1 l2,
        i = length l1 ->
        @try_take_n A i (l1 ++ l2) = (l1, IoLR A l2).
Proof.
    move=> i l1 l2; move: l1; induction i as [|i HRec]; simpl.
    {
        move=> []; simpl; trivial.
        by discriminate.
    }
    {
        move=> [|hd tl]; simpl.
        by discriminate.
        specialize HRec with tl.
        move=> HEq; move: HRec.
        impl_tac.
        + inversion HEq; reflexivity.
        + move=> ->; reflexivity.
    }
Qed.

(* build_ctxt and auxiliairies properties *)


Theorem build_ctxt_aux_take_n_soundness:
    forall d iL_tl n iL,
        length iL = n ->
        iL_tl <> nil ->
        build_ctxt_aux_take_n n (CoIR d (iL ++ iL_tl) None::nil) d
            = Some (iL, CoIR d iL_tl None::nil).
Proof.
    intros d iL_tl n; induction n as [|n HRec]; simpl.
    all: intro iL; destruct iL as [|hd iL]; simpl; trivial.
    1-2: discriminate.
    rewrite internal_dir_dec_lb0; trivial.
    intro H; inversion H as [HEq]; clear H.
    rewrite try_take_n_soundness; trivial.
    destruct iL_tl; trivial.
    intro H; exfalso; apply H; reflexivity.
Qed.

Theorem build_ctxt_aux_take_n_soundness2:
    forall d n iL,
        length iL = n ->
        n <> 0 ->
        build_ctxt_aux_take_n n (CoIR d iL None::nil) d
            = Some (iL, nil).
Proof.
    intros d n iL LengthEq; simpl.
    unfold build_ctxt_aux_take_n.
    rewrite internal_dir_dec_lb0; trivial.
    rewrite try_take_n_all; auto.
    destruct n; trivial.
    intro H; exfalso; apply H; auto.
Qed.

(* properties about undefined *)

Lemma length_undefined {A : Type} :
    forall n, length (@undefined A n) = n.
Proof.
    intro n; induction n as [|n HRec]; simpl; auto.
Qed.

Lemma undefined_sum {A : Type}:
    forall n1 n2,
        @undefined A (n1 + n2) = undefined n1 ++ undefined n2.
Proof.
    intros n n2; induction n as [|n HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Lemma undefined_lemma {A : Type}:
    forall n1 n2,
    concat (map (fun _=> @undefined A n2) (@undefined A n1)) = undefined (n2 * n1)%coq_nat.
Proof.
    intros n1 n2; induction n1 as [|n1 HRec]; simpl.
    {
        rewrite Nat.mul_0_r; auto.
    }
    {
        rewrite Nat.mul_succ_r.
        rewrite Nat.add_comm.
        rewrite undefined_sum.
        rewrite HRec; reflexivity.
    }
Qed.

(* split_into_segments properties *)

Lemma split_into_segments_soundness {A : Type} :
    forall i1 i2 l,
        length l = i1 * i2 ->
        exists l', @split_into_segments A i1 i2 l = Some l' /\
            Forall (fun l => length l = i2) l' /\
            List.concat l' = l /\ length l' = i1.
Proof.
    move=> i1 i2; induction i1 as [|i1 HRec]; simpl.
    {
        move=> l.
        unfold muln, muln_rec.
        rewrite Nat.mul_0_l.
        destruct l; simpl.
        2: by discriminate.
        move=> _; exists nil; simpl.
        auto.
    }
    {
        move=> l length_eq.
        pose (p:= take_n_soundness i2 l); move: p.
        impl_tac.
        {
            rewrite length_eq; clear.
            rewrite mulSnr.
            apply leq_addl.
        }
        move=> [l1 [l2 [HEq1 [HEq2 LengthEq]]]].
        rewrite HEq1.
        rewrite HEq2 in length_eq; rewrite HEq2; clear HEq2 HEq1 l.
        specialize HRec with l2; move: HRec; impl_tac.
        {
            rewrite mulSnr in length_eq.
            refine (length_app_eq _ _ _ _ LengthEq _).
            rewrite addnC.
            assumption.
        }
        move=> [l [-> [HForall [concat_eq length_eq3]]]].
        exists (l1::l); simpl.
        rewrite concat_eq.
        repeat split; auto.
    }
Qed.

Lemma split_into_segments_soundness2 {A : Type} :
    forall i1 i2 l,
        length l = i1 * i2 ->
        exists l', @split_into_segments (option A) i1 i2 (List.map Some l) = Some (List.map (List.map Some) l') /\
            Forall (fun l => length l = i2) l' /\
            List.concat l' = l /\ length l' = i1.
Proof.
    move=> i1 i2; induction i1 as [|i1 HRec]; simpl.
    {
        move=> l.
        unfold muln, muln_rec.
        rewrite Nat.mul_0_l.
        destruct l; simpl.
        2: by discriminate.
        move=> _; exists nil; simpl.
        auto.
    }
    {
        move=> l length_eq.
        pose (p:= take_n_soundness2 i2 l); move: p.
        impl_tac.
        {
            rewrite length_eq; clear.
            rewrite mulSnr.
            apply leq_addl.
        }
        move=> [l1 [l2 [HEq1 [HEq2 LengthEq]]]].
        rewrite HEq1.
        symmetry in HEq2; destruct HEq2.
        specialize HRec with l2; move: HRec; impl_tac.
        {
            rewrite mulSnr in length_eq.
            refine (length_app_eq _ _ _ _ LengthEq _).
            rewrite addnC.
            assumption.
        }
        move=> [l [-> [HForall [concat_eq length_eq3]]]].
        exists (l1::l); simpl.
        rewrite concat_eq.
        repeat split; auto.
    }
Qed.


Lemma split_into_segments_1_r {A : Type}:
    forall l : list A, forall n,
        length l = n -> split_into_segments n 1 l = Some (List.map (fun i => [:: i]) l).
Proof.
    move=> l; induction l as [|hd l HRec]; simpl.
    by move=> n <-; simpl; reflexivity.
    move=> [|n].
    by discriminate.
    move=> HEq; inversion HEq; clear HEq; simpl.
    rewrite HRec; auto.
Qed.

Lemma split_into_segments_1_l {A : Type}:
    forall l : list A, forall n,
        length l = n -> split_into_segments 1 n l = Some [:: l].
Proof.
    simpl.
    move=> l n length_eq.
    rewrite take_n_all; trivial.
Qed.


Theorem split_into_segments_undefined {A : Type} :
    forall n1 n2,
        split_into_segments n1 n2 (@undefined A (n1 * n2)) = Some (map (fun _=> undefined n2) (@undefined A n1)).
Proof.
    intro n1; induction n1 as [|n1 HRec]; simpl; trivial.
    intro; rewrite undefined_sum.
    rewrite take_n_sum.
    2: exact (length_undefined _).
    rewrite HRec; reflexivity.
Qed.
    
(* other lemmas *)

Theorem remove_option_from_list_map_Some {A : Type}:
    forall l, @remove_option_from_list A (map Some l) = Some l.
Proof.
    intro l; induction l as [|hd tl HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Theorem get_access_AAll:
    forall n l, length l = n -> n <> 0 -> get_access (map Some l) AAll (n::nil) = Some l.
Proof.
    intros n l lengthEq NotZero; simpl.
    apply remove_option_from_list_map_Some.
Qed.

Theorem list_map2_soundness {A B C : Type}:
    forall (f : A -> B -> C) l1 l2, length l1 = length l2 ->
        exists l3, length l3 = length l1 /\ list_map2 f l1 l2 = Some l3.
Proof.
    intros f l1; induction l1 as [|h1 t1 HRec]; simpl.
    {
        intro l2; destruct l2; simpl.
        + intro; exists nil; auto.
        + discriminate.
    }
    {
        intro l2; destruct l2 as [|h2 t2]; simpl.
        { discriminate. }
        intro H; inversion H as [length_eq].
        destruct (HRec _ length_eq) as [l3 [<- ->]].
        exists (f h1 h2::l3); auto.
    }
Qed.
