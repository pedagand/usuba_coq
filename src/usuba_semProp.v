Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils usuba_AST usuba_sem coq_missing_lemmas.

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
        unfold muln, muln_rec; rewrite PeanoNat.Nat.mul_1_l; reflexivity.
    + rewrite <- HRec; reflexivity.
Qed.

Lemma prod_list_append:
    forall l1 l2,
        prod_list (l1 ++ l2)%list = prod_list l1 * prod_list l2.
Proof.
    move=> l1; induction l1 as [|hd l1 HRec]; simpl; move=> l2.
    {
        unfold muln, muln_rec; rewrite PeanoNat.Nat.mul_1_l; reflexivity.
    }
    {
        rewrite HRec.
        unfold muln, muln_rec; rewrite PeanoNat.Nat.mul_assoc; reflexivity.
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
        case (String.eqb x n).
        + discriminate.
        + assumption.
    }
    {
        move=> ctxt2.
        case (String.eqb x n1); auto.
        induction ctxt2 as [|[n2 v2] ctxt2 HRec2]; simpl.
        + discriminate.
        + case (String.eqb x n2).
            - move=> HEq; inversion HEq; reflexivity.
            - assumption.
    }
Qed.

(* linearize_list_value properties *)

Lemma map_CoIL_is_lin:
    forall l, linearize_list_value [seq CoIL i | i <- l] nil = [seq CoIL i | i <- l].
Proof.
    move=> l; induction l as [|hd tl HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Theorem linearize_map_CoIL:
    forall l1 l2, linearize_list_value (map CoIL l1) l2 = (map CoIL l1) ++ l2.
Proof.
    move=> l1 l2; induction l1 as [|hd l1 HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Theorem eval_var_linearize_fixpoint:
    forall ctxt v acc l, eval_var ctxt v acc = Some l -> linearize_list_value l nil = l.
Proof.
    move=> ctxt; induction v as [v|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl; move=> acc l.
    {
        destruct (find_val ctxt v) as [[cst|dir iL [dim|]]|].
        3-4: discriminate.
        {
            case (get_access [:: cst] acc nil); case acc.
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

Lemma split_into_segments_1_r {A : Type}:
    forall l : list A, forall n,
        length l = n -> split_into_segments n 1 l = Some (map (fun i => [:: i]) l).
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
