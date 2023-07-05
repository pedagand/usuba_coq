Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST usuba_ASTProp arch
    list_relations termination_funs termination_properties
    semantic_base semantic_base_proofs.

Lemma list_def_tree_of_type_length:
    forall typ trees len,
        list_def_tree_of_type trees typ len -> dtrees_length trees = len.
Proof.
    move=> typ; induction trees as [|hd tl HRec]; simpl; auto.
    move=> [|len] [_ H]; [> by destruct H | f_equal; auto ].
Qed.

(* Properties about subtrees *)

Lemma sub_dtree_refl {A}:
    forall t, @sub_dtree A t t.
Proof.
    refine (def_tree_find _ _ (fun t => sub_dtrees t t) _ _ _ _).
    all: by intros; constructor.
Qed.

Lemma sub_dtree_trans {A}:
    forall x y z, sub_dtree x y -> sub_dtree y z -> @sub_dtree A x z.
Proof.
    move=> x y z H; move: x y H z.
    refine (sub_dtree_find _ _ (fun l1 l2 H1 => forall l3, sub_dtrees l2 l3 -> sub_dtrees l1 l3) _ _ _ _).
    by intros; constructor.
    {
        move=> l1 l2 H12 HRec t3 H23; inversion H23.
        constructor; auto.
    }
    {
        move=> l3 H; inversion H; constructor.
    }
    {
        move=> h1 h2 t1 t2 hd12 HRec_hd tl12 HRec_tl l3 H; inversion H.
        constructor; auto.
    }
Qed.

Lemma sub_dtrees_length {A} :
    forall l1 l2,
        @sub_dtrees A l1 l2 -> dtrees_length l1 = dtrees_length l2.
Proof.
    move=> l1; induction l1 as [|h1 t2 HRec]; simpl.
    all: move=> l2 H; inversion H; simpl; auto.
Qed.

Lemma sub_dtree_keep_access {A} :
    forall path t1 t2,
        valid_dtree_access t1 path ->
        @sub_dtree A t1 t2 ->
        valid_dtree_access t2 path.
Proof.
    move=> path; induction path as [|ind tl HRec].
    by move=> [b1|t1] [b2|t2]; simpl; trivial.
    move=> [b1|t1] t2' valid1 H; simpl in valid1.
    by discriminate.
    inversion H as [|l1 l2 sub_l H1 H2]; destruct H1; destruct H2; clear H.
    simpl; destruct ind as [ae|ae1 ae2|aeL].
    {
        destruct eval_arith_expr as [i|]; [> idtac | by idtac ].
        destruct valid1 as [H0 [H1 H2]].
        rewrite <-(sub_dtrees_length _ _ sub_l); split; trivial.
        split; trivial.
        move: sub_l HRec H2; clear; move=> sub_l Himp.
        pose (p := 0); fold p; move: p.
        induction sub_l as [|h1 h2 t1 t2 sub_hd sub_tl HRec]; simpl; trivial.
        move=> pos [valid1 H]; split; auto.
        destruct (_ =? _); simpl in *; trivial.
        apply (Himp h1); trivial.
    }
    {
        destruct eval_arith_expr; [> idtac | by idtac ].
        destruct eval_arith_expr; [> idtac | by idtac ].
        destruct valid1 as [H0 [H1 H2]].
        rewrite <-(sub_dtrees_length _ _ sub_l); split; trivial.
        split; trivial.
        move: sub_l HRec H2; clear; move=> sub_l Himp.
        pose (p := 0); fold p; move: p.
        induction sub_l as [|h1 h2 t1 t2 sub_hd sub_tl HRec]; simpl; trivial.
        move=> pos [valid1 H]; split; auto.
        destruct List.existsb; simpl in *; trivial.
        apply (Himp h1); trivial.
    }
    {
        destruct fold_right; [> idtac | by idtac ].
        destruct valid1 as [H0 [H1 H2]].
        rewrite <-(sub_dtrees_length _ _ sub_l); split; trivial.
        split; trivial.
        move: sub_l HRec H2; clear; move=> sub_l Himp.
        pose (p := 0); fold p; move: p.
        induction sub_l as [|h1 h2 t1 t2 sub_hd sub_tl HRec]; simpl; trivial.
        move=> pos [valid1 H]; split; auto.
        destruct List.existsb; simpl in *; trivial.
        apply (Himp h1); trivial.
    }
Qed.

(* same tree proofs *)

Lemma same_dtrees_length {A B}:
    forall dtrees1 dtrees2,
        @same_dtrees A B dtrees1 dtrees2 ->
        dtrees_length dtrees1 = dtrees_length dtrees2.
Proof.
    move=> d1 d2 same; induction same; simpl; auto.
Qed.

Lemma keep_valid_acces_change_dtree {A B}:
    forall dtree1 dtree2,
        @same_dtree A B dtree1 dtree2 ->
        forall acc,
            valid_dtree_access dtree1 acc ->
            valid_dtree_access dtree2 acc.
Proof.
    move=> dtree1 dtree2 same acc.
    move: dtree1 dtree2 same.
    induction acc as [|hd tl HRec].
    all: move=> t1 t2 same; inversion same as [|trees1 trees2 same']; simpl.
    1-3: by trivial.
    match goal with |- _ -> match ?iLdef with | Some iL => _ | None => False end =>
        destruct iLdef as [iL|]; [> idtac | by trivial ]
    end.
    rewrite (same_dtrees_length _ _ same').
    move=> [not_empty [all_inf valid]]; split; [> assumption | idtac ].
    split; [> assumption | idtac ].
    move: HRec same' valid; clear.
    move=> HRec same'.
    pose (pos := 0); fold pos; move: pos.
    induction same'; simpl; trivial.
    move=> pos; destruct List.existsb; trivial.
    all: move=> [valid_tl valid_hd]; split; auto.
    refine (HRec _ _ _ valid_hd); assumption.
Qed.


(* Soundness of functions *)

Lemma dtrees_length_build {A}:
    forall len pos indices t1 t2,
    @dtrees_length A (build_def_trees pos len indices t1 t2) = len.
Proof.
    move=> len; induction len as [|len HRec]; simpl; trivial.
    move=> pos indices t1 t2; destruct List.existsb; simpl; rewrite add1n.
    all: rewrite HRec; reflexivity.
Qed.

Lemma build_def_tree_from_type_access:
    forall path_tl len_eqns_hd typ tree',
        build_def_tree_from_type path_tl typ len_eqns_hd = Some tree' ->
            valid_dtree_access tree' path_tl.
Proof.
    move=> path_tl len_eqns_hd.
    induction path_tl as [|ind path_tl HRec]; simpl.
    {
        move=> typ tree' H.
        inversion H as [H']; clear H H' tree'.
        simpl; trivial.
    }
    {
        move=> [|d m|typ len].
        1,2: by idtac.
        move: (HRec typ); clear HRec; move=> HRec.
        destruct build_def_tree_from_type as [next_tree|].
        2: by idtac.
        destruct ind as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i HEq; simpl | by idtac].
            case_eq (i <? len); [> move=> HInf; simpl | by idtac ].
            move=> tree' H.
            inversion H as [H']; clear H H' tree'; simpl.
            specialize HRec with next_tree.
            rewrite Nat.ltb_lt in HInf.
            rewrite HEq; split; [> by discriminate | split ].
            {
                constructor; [> idtac | by constructor ].
                rewrite dtrees_length_build; apply/ltP; assumption.
            }
            {
                move: HRec; clear.
                impl_tac; trivial.
                move=> valid_access.
                pose (p := 0); fold p; move: p.
                induction len as [|len HRec]; simpl; trivial.
                move=> pos; case_eq (pos =? i); simpl.
                all: move=> H; rewrite H; simpl.
                all: split; trivial.
            }
        }
        {
            by idtac.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            case_eq (forallb (Nat.ltb^~ len) iL && List.existsb xpredT iL); [> move=> AllInf; simpl | by idtac ].
            move=> tree' H.
            inversion H as [H']; clear H H' tree'.
            specialize HRec with next_tree; simpl.
            rewrite HEq; rewrite dtrees_length_build.
            move/andP in AllInf; unfold is_true in AllInf.
            destruct AllInf as [AllInf NotEmpty].
            split.
            {
                move=> H; rewrite H in NotEmpty; simpl in NotEmpty.
                inversion NotEmpty.
            }
            split.
            {
                move: AllInf; clear.
                rewrite List.forallb_forall; rewrite List.Forall_forall.
                move=> H x LIn; apply H in LIn; move: LIn.
                rewrite Nat.ltb_lt; move/ltP; trivial.
            }
            {
                move: HRec; clear.
                impl_tac; trivial.
                move=> valid_access.
                pose (pos := 0); fold pos; move: pos.
                induction len as [|len HRec]; simpl; trivial.
                move=> pos.
                case_eq (List.existsb (Nat.eqb pos) iL); simpl; move=>->; auto.
            }
        }
    }
Qed.

Lemma build_def_tree_from_type_type_soundness:
    forall path_tl len_eqns_hd typ tree',
        build_def_tree_from_type path_tl typ len_eqns_hd = Some tree' ->
            def_tree_of_type tree' typ.
Proof.
    move=> path_tl len_eqns_hd.
    induction path_tl as [|ind path_tl HRec]; simpl.
    {
        move=> typ tree' H.
        inversion H as [H']; clear H H' tree'.
        simpl; trivial.
    }
    {
        move=> [|d m|typ len].
        1,2: by idtac.
        move: (HRec typ); clear HRec; move=> HRec.
        destruct build_def_tree_from_type as [next_tree|].
        2: by idtac.
        destruct ind as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i HEq; simpl | by idtac].
            case_eq (i <? len); [> move=> HInf; simpl | by idtac ].
            move=> tree' H.
            inversion H as [H']; clear H H' tree'; simpl.
            move: (HRec next_tree); clear.
            impl_tac; trivial.
            move=> type_of_tree.
            pose (p:= 0); fold p; move: p.
            induction len; simpl; trivial.
            move=> p; destruct (_ || _); simpl; auto.
        }
        {
            by idtac.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            case_eq (forallb (Nat.ltb^~ len) iL && List.existsb xpredT iL); [> move=> AllInf; simpl | by idtac ].
            move=> tree' H.
            inversion H as [H']; clear H H' tree'.
            specialize HRec with next_tree; simpl.
            move: HRec; impl_tac; trivial; clear.
            pose (p:= 0); fold p; move: p.
            induction len; simpl; trivial.
            move=> p; destruct List.existsb; simpl; auto.
        }
    }
Qed.

Lemma build_def_tree_from_type_soundness:
    forall path_tl eqns_hd typ tree',
        build_def_tree_from_type path_tl typ (length eqns_hd) = Some tree' ->
            forall vars_hd vars_tl eqns_tl expr v path_in path_nat,
                list_rel is_specialization path_nat path_in ->
                (forall (l' : seq nat),
                    list_rel_top eq path_nat l' ->
                    partial_defined_in (length vars_hd + 1) v l' (length eqns_hd) (eqns_hd ++ (vars_hd ++ Index (Var v) (path_in ++ path_tl) :: vars_tl, expr) :: eqns_tl) -> False) ->
                (forall (pos : nat) (l' : seq nat), list_rel_top eq path_nat l' -> length eqns_hd < pos ->
                    defined_in v l' pos (eqns_hd ++ (vars_hd ++ Index (Var v) (path_in ++ path_tl) :: vars_tl, expr) :: eqns_tl) -> False) ->
                partial_valid_def_tree' (length eqns_hd) (length vars_hd) v tree' path_nat
                (eqns_hd ++
                (vars_hd ++ Index (Var v) (path_in ++ path_tl) :: vars_tl, expr)
                :: eqns_tl).
Proof.
    move=> path_tl eqns_hd.
    induction path_tl as [|ind path_tl HRec]; simpl.
    {
        move=> typ tree' H.
        inversion H as [H']; clear H H' tree'.
        move=> vars_hd vars_tl eqns_tl expr v path_in path_nat is_spec not_partial_defined not_defined.
        split; trivial.
        move=> pos l' Hinf top_eq.
        destruct (leq_Cases _ _ Hinf) as [Heq|Hinf'].
        {
            destruct Heq; split.
            {
                move=> [_ HEq]; rewrite Nat.eqb_refl; destruct HEq.
                unfold partial_defined_in.
                rewrite nth_error_app2; trivial.
                rewrite Nat.sub_diag; simpl.
                do 3 eexists; repeat split.
                by exact is_spec.
                exists (length vars_hd); split; trivial.
                left; rewrite nth_error_app2; trivial.
                rewrite Nat.sub_diag; simpl.
                rewrite cats0; reflexivity.
            }
            {
                rewrite Nat.eqb_refl.
                move: (not_partial_defined _ top_eq); clear not_partial_defined.
                move=> not_partial_defined partial_defined; move: partial_defined not_partial_defined.
                unfold partial_defined_in.
                rewrite cats0; rewrite nth_error_app2; trivial.
                rewrite Nat.sub_diag; simpl.
                move=> [vL [e [ind [HEq [is_spec' [i [len_vars_inf HEq_var]]]]]]] not_pdef.
                split; [> reflexivity | idtac ].
                inversion HEq as [[H1 H2]]; destruct H1; destruct H2.
                destruct (leq_Cases _ _ len_vars_inf) as [len_vars_eq|len_vars_sinf].
                {
                    rewrite <-list_rel_eq_is_eq.
                    apply list_rel_top_same_length; trivial.
                    destruct len_vars_eq.
                    rewrite nth_error_app2 in HEq_var; trivial.
                    rewrite Nat.sub_diag in HEq_var; simpl in HEq_var.
                    move: is_spec.
                    destruct HEq_var as [H|[H _]]; inversion H.
                    move=> is_spec2.
                    apply list_rel_length in is_spec2; rewrite is_spec2.
                    apply list_rel_length in is_spec'; rewrite is_spec'.
                    reflexivity.
                }
                {
                    exfalso; apply not_pdef.
                    do 3 eexists; repeat split.
                    by exact is_spec'.
                    exists i; rewrite addn1.
                    split; assumption.
                }
            }
        }
        specialize not_defined with pos l'.
        move: not_defined; impl_tac; trivial.
        impl_tac; trivial.
        move=> not_defined.
        split.
        {
            move=> [H H']; symmetry in H; destruct H; destruct H'.
            by rewrite ltnn in Hinf'.
        }
        case_eq (pos =? length eqns_hd).
        {
            rewrite Nat.eqb_eq.
            move=> H; symmetry in H; destruct H.
            move: (not_partial_defined _ top_eq); clear not_partial_defined.
            move=> not_partial_defined partial_defined; move: partial_defined not_partial_defined.
            unfold partial_defined_in.
            rewrite cats0; rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            move=> [vL [e [ind [HEq [is_spec' [i [len_vars_inf HEq_var]]]]]]] not_pdef.
            split; [> reflexivity | idtac ].
            inversion HEq as [[H1 H2]]; destruct H1; destruct H2.
            destruct (leq_Cases _ _ len_vars_inf) as [len_vars_eq|len_vars_sinf].
            {
                rewrite <-list_rel_eq_is_eq.
                apply list_rel_top_same_length; trivial.
                destruct len_vars_eq.
                rewrite nth_error_app2 in HEq_var; trivial.
                rewrite Nat.sub_diag in HEq_var; simpl in HEq_var.
                move: is_spec.
                destruct HEq_var as [H|[H _]]; inversion H.
                move=> is_spec2.
                apply list_rel_length in is_spec2; rewrite is_spec2.
                apply list_rel_length in is_spec'; rewrite is_spec'.
                reflexivity.
            }
            {
                exfalso; apply not_pdef.
                do 3 eexists; repeat split.
                by exact is_spec'.
                exists i; rewrite addn1.
                split; assumption.
            }
        }
        {
            move=> _.
            rewrite cats0 in not_defined.
            rewrite cats0.
            move=> Abs; apply not_defined in Abs; destruct Abs.
        }
    }
    {
        move=> [|d m|typ len].
        1,2: by idtac.
        move: (HRec typ); clear HRec; move=> HRec.
        destruct build_def_tree_from_type as [next_tree|].
        2: by idtac.
        destruct ind as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i HEq; simpl | by idtac].
            case_eq (i <? len); [> move=> HInf; simpl | by idtac ].
            move=> tree' H.
            inversion H as [H']; clear H H' tree'; simpl.
            move: (HRec next_tree); clear HRec.
            impl_tac; trivial.
            move=> HRec vars_hd vars_tl eqns_tl expr v path_in path_nat is_spec.
            move: (HRec vars_hd vars_tl eqns_tl expr v (path_in ++ [:: IInd ae]) (path_nat ++ [:: i])); clear HRec.
            impl_tac.
            {
                apply list_rel_last; split; trivial.
                constructor; assumption.
            }
            rewrite <- app_assoc; simpl.
            move=> H not_partial_defined not_defined.
            move: H; impl_tac.
            {
                move=> l' top_eq.
                specialize not_partial_defined with l'.
                apply not_partial_defined.
                exact (list_rel_top_eq _ _ _ top_eq).
            }
            impl_tac.
            {
                move=> pos l' top_eq.
                specialize not_defined with pos l'.
                apply not_defined.
                exact (list_rel_top_eq _ _ _ top_eq).
            }
            move=> H.
            split.
            {
                move: (not_partial_defined path_nat) is_spec; clear.
                impl_tac.
                by induction path_nat; constructor; trivial.
                unfold partial_defined_in.
                rewrite nth_error_app2; auto.
                rewrite Nat.sub_diag; simpl.
                move=> not_partial_defined is_spec_raw [vL [e' [ind [HEq [is_spec [i [HInf HEq']]]]]]].
                apply not_partial_defined; clear not_partial_defined.
                do 3 eexists; repeat split.
                by exact is_spec.
                move: HInf HEq' is_spec is_spec_raw; inversion HEq; clear.
                move=> HInf.
                destruct (leq_Cases _ _ HInf) as [HEq|HInf'].
                {
                    destruct HEq.
                    rewrite nth_error_app2; trivial; rewrite Nat.sub_diag; simpl.
                    move=> H lrel1 lrel2.
                    apply list_rel_length in lrel1.
                    apply list_rel_length in lrel2.
                    rewrite lrel2 in lrel1; exfalso; move: lrel1.
                    destruct H as [H'|[H' _]]; inversion H'.
                    rewrite app_length; simpl.
                    clear.
                    induction (length path_in) as [|l HRec]; simpl.
                    by idtac.
                    move=> H; apply HRec; inversion H as [H'].
                    do 2 rewrite <- H'; reflexivity.
                }
                rewrite addn1.
                move=> H _ _; exists i; split; trivial.
            }
            {
                split.
                {
                    move=> pos; specialize not_defined with pos path_nat.
                    apply not_defined; clear.
                    induction path_nat; constructor; trivial.
                }
                pose (pos := 0); fold pos; move: pos.
                clear HInf.
                induction len as [|len HRec]; simpl.
                {
                    move=> _; split; auto.
                }
                move=> pos; specialize HRec with pos.+1.
                rewrite orb_false_r.
                case_eq (pos =? i); simpl.
                by rewrite Nat.eqb_eq; move=> Eq; destruct Eq; auto.
                move=> HNeq.
                repeat split; trivial.
                {
                    move=> l' top_eq.
                    specialize not_partial_defined with l'.
                    move: top_eq HNeq (not_partial_defined (list_rel_top_eq _ _ _ top_eq)) is_spec HEq; clear.
                    rewrite <-not_true_iff_false; rewrite Nat.eqb_eq.
                    unfold partial_defined_in.
                    rewrite nth_error_app2; trivial.
                    rewrite Nat.sub_diag; simpl.
                    move=> top_eq HNeq not_partial is_spec' eval_eq [vL [e' [ind [HEq [is_spec [i' [HInf HEq']]]]]]].
                    apply not_partial.
                    do 3 eexists; repeat split.
                    by exact is_spec.
                    move: HEq'; inversion HEq; clear HEq.
                    destruct (leq_Cases _ _ HInf) as [<-|HInf'].
                    {
                        rewrite nth_error_app2; trivial.
                        rewrite Nat.sub_diag; simpl.
                        apply list_rel_length in is_spec'.
                        move=> H.
                        move: is_spec.
                        destruct H as [H'|[H' _]]; inversion H' as [H2].
                        clear H' H2 ind.
                        move=> is_spec.
                        exfalso; apply HNeq.
                        move: top_eq is_spec' is_spec eval_eq; clear.
                        move: path_nat path_in.
                        induction l' as [|l_hd l_tl HRec].
                        {
                            move=> path_nat [|pin_hd pin_tl] _ _ H; simpl in *; inversion H.
                        }
                        {
                            move=> [|pnat_hd pnat_tl] [|pin_hd pin_tl] top_eq length_eq; simpl in *.
                            all: inversion length_eq as [length_eq'].
                            all: move=> H; inversion H as [|h1 h2 t1 t2 rel_hd rel_tl]; clear H.
                            {
                                inversion rel_hd as [ae' i' eval_eq| |]; rewrite eval_eq.
                                inversion top_eq as [| |h3 h4 t3 t4 HEq]; destruct HEq.
                                move=> eq_some; inversion eq_some; reflexivity.
                            }
                            {
                                inversion top_eq.
                                apply (HRec pnat_tl pin_tl); trivial.
                            }
                        }
                    }
                    {
                        intro; exists i'.
                        rewrite addn1; auto.
                    }
                }
                {
                    move=> pos' l' top_eq.
                    apply not_defined.
                    exact (list_rel_top_eq _ _ _ top_eq).
                }
            }
        }
        {
            by idtac.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            case_eq (forallb (Nat.ltb^~ len) iL && List.existsb xpredT iL); [> move=> AllInf; simpl | by idtac ].
            move=> tree' H.
            inversion H as [H']; clear H H' tree'.
            move=> vars_hd vars_tl eqns_tl expr v path_in path_nat is_spec.
            move: (HRec _ (Logic.eq_refl _) vars_hd vars_tl eqns_tl expr v (path_in ++ [:: ISlice aeL])); clear HRec.
            rewrite <- app_assoc; simpl.
            move=> H not_partial_defined not_defined.
            split.
            {
                clear AllInf.
                move: (not_partial_defined path_nat) is_spec; clear.
                impl_tac.
                by induction path_nat; constructor; trivial.
                unfold partial_defined_in.
                rewrite nth_error_app2; auto.
                rewrite Nat.sub_diag; simpl.
                move=> not_partial_defined is_spec_raw [vL [e' [ind [HEq [is_spec [i [HInf HEq']]]]]]].
                apply not_partial_defined; clear not_partial_defined.
                do 3 eexists; repeat split.
                by exact is_spec.
                move: HInf HEq' is_spec is_spec_raw; inversion HEq; clear.
                move=> HInf.
                destruct (leq_Cases _ _ HInf) as [HEq|HInf'].
                {
                    destruct HEq.
                    rewrite nth_error_app2; trivial; rewrite Nat.sub_diag; simpl.
                    move=> H lrel1 lrel2.
                    apply list_rel_length in lrel1.
                    apply list_rel_length in lrel2.
                    rewrite lrel2 in lrel1; exfalso; move: lrel1.
                    destruct H as [H'|[H' _]]; inversion H'.
                    rewrite app_length; simpl.
                    clear.
                    induction (length path_in) as [|l HRec]; simpl.
                    by idtac.
                    move=> H; apply HRec; inversion H as [H'].
                    do 2 rewrite <- H'; reflexivity.
                }
                rewrite addn1.
                move=> H _ _; exists i; split; trivial.
            }
            {
                clear AllInf; split.
                {
                    move=> pos; specialize not_defined with pos path_nat.
                    apply not_defined; clear.
                    induction path_nat; constructor; trivial.
                }
                pose (pos := 0); fold pos; move: pos.
                induction len as [|len HRec]; simpl; trivial.
                move=> pos; specialize HRec with pos.+1.
                case_eq (List.existsb (Nat.eqb pos) iL).
                {
                    move=> Hmem; simpl; split; trivial.
                    apply H.
                    all: swap 1 2.
                    {
                        move=> l' top_eq; apply not_partial_defined.
                        exact (list_rel_top_eq _ _ _ top_eq).
                    }
                    all: swap 1 2.
                    {
                        move=> pos' l' top_eq; apply not_defined.
                        exact (list_rel_top_eq _ _ _ top_eq).
                    }
                    assert (exists ae, List.In ae aeL /\ eval_arith_expr nil ae = Some pos) as HIn.
                    {
                        move: HEq Hmem; clear; move: iL.
                        induction aeL as [|hd tl HRec]; simpl.
                        {
                            move=> iL H; inversion H.
                            by simpl.
                        }
                        {
                            move=> iL.
                            destruct fold_right as [l|].
                            2: by idtac.
                            specialize HRec with l.
                            case_eq (eval_arith_expr nil hd); [> move=> i HEq | by idtac].
                            move=> H; inversion H as [H']; clear H H' iL; simpl.
                            move :(orb_prop_elim (pos =? i) (List.existsb (Nat.eqb pos) l)).
                            move=> H_or H; rewrite H in H_or; clear H.
                            move: H_or; impl_tac; simpl; trivial.
                            move=> [H|H]; apply Is_true_eq_true in H.
                            {
                                rewrite Nat.eqb_eq in H; destruct H.
                                exists hd; auto.
                            }
                            destruct HRec as [ae [HIn eval_eq]]; trivial.
                            exists ae; auto.
                        }
                    }
                    destruct HIn as [ae [HIn eval_eq]].
                    rewrite list_rel_last; split; auto.
                    apply (SpecSlice ae); trivial.
                }
                {
                    move=> exists_false; simpl; repeat split; trivial.
                    {
                        move=> l' top_eq.
                        specialize not_partial_defined with l'.
                        move: top_eq exists_false (not_partial_defined (list_rel_top_eq _ _ _ top_eq)) is_spec HEq; clear.
                        rewrite <-not_true_iff_false; rewrite existsb_exists.
                        unfold partial_defined_in.
                        rewrite nth_error_app2; trivial.
                        rewrite Nat.sub_diag; simpl.
                        move=> top_eq HNeq not_partial is_spec' eval_eq [vL [e' [ind [HEq [is_spec [i' [HInf HEq']]]]]]].
                        apply not_partial.
                        do 3 eexists; repeat split.
                        by exact is_spec.
                        move: HEq'; inversion HEq; clear HEq.
                        destruct (leq_Cases _ _ HInf) as [<-|HInf'].
                        {
                            rewrite nth_error_app2; trivial.
                            rewrite Nat.sub_diag; simpl.
                            apply list_rel_length in is_spec'.
                            move=> H.
                            move: is_spec.
                            destruct H as [H'|[H' _]]; inversion H' as [H2].
                            clear H' H2 ind.
                            move=> is_spec.
                            exfalso; apply HNeq.
                            move: top_eq is_spec' is_spec eval_eq; clear.
                            move: path_nat path_in.
                            induction l' as [|l_hd l_tl HRec].
                            {
                                move=> path_nat [|pin_hd pin_tl] _ _ H; simpl in *; inversion H.
                            }
                            {
                                move=> [|pnat_hd pnat_tl] [|pin_hd pin_tl] top_eq length_eq; simpl in *.
                                all: inversion length_eq as [length_eq'].
                                all: move=> H; inversion H as [|h1 h2 t1 t2 rel_hd rel_tl]; clear H.
                                {
                                    inversion rel_hd as [|ae aeL' i LIn eval_eq|].
                                    inversion top_eq as [| |h3 h4 t3 t4 HEq]; destruct HEq.
                                    move=> fold_eq; exists pos.
                                    split; [> idtac | apply Nat.eqb_refl ].
                                    move: LIn fold_eq eval_eq; clear.
                                    move: iL.
                                    induction aeL as [|ae_hd ae_tl HRec]; simpl.
                                    by move=> iL [].
                                    move=> iL [<-|LIn].
                                    all: destruct fold_right.
                                    2,4: by move=> H; inversion H.
                                    all: destruct (eval_arith_expr nil ae_hd); move=> H; inversion H as [H'].
                                    {
                                        move=> H2; inversion H2; simpl.
                                        left; reflexivity.
                                    }
                                    {
                                        move=> eval_eq; simpl; right.
                                        refine (HRec _ LIn Logic.eq_refl eval_eq).
                                    }
                                }
                                {
                                    inversion top_eq.
                                    apply (HRec pnat_tl pin_tl); trivial.
                                }
                            }
                        }
                        {
                            intro; exists i'.
                            rewrite addn1; auto.
                        }
                    }
                    {
                        move=> pos' l' top_eq; apply not_defined.
                        exact (list_rel_top_eq _ _ _ top_eq).
                    }
                }
            }
        }
    }
Qed.

Lemma partial_valid_def_tree'_decr:
    forall eqns_hd eqns_tl vars_hd vars_tl expr v tree pnat1 pnat2 pnat3 pin1 pin2 pin3 path_tl,
        partial_valid_def_tree' (length eqns_hd) (length vars_hd + 1) v tree (pnat1 ++ pnat2 :: pnat3) (eqns_hd ++ (vars_hd ++ Index (Var v) (pin1 ++ pin2 :: pin3 ++ path_tl) :: vars_tl, expr) :: eqns_tl) ->
        (list_rel is_specialization pnat1 pin1) ->
        (is_specialization pnat2 pin2 -> False) ->
        partial_valid_def_tree' (length eqns_hd) (length vars_hd) v tree (pnat1 ++ pnat2 :: pnat3) (eqns_hd ++ (vars_hd ++ Index (Var v) (pin1 ++ pin2 :: pin3 ++ path_tl) :: vars_tl, expr) :: eqns_tl).
Proof.
    move=> eqns_hd eqns_tl vars_hd vars_tl expr v tree pnat1 pnat2 pnat3 pin1 pin2 pin3 path_tl pval is_spec not_spec.
    move: tree pnat3 pin3 path_tl pval.
    refine (def_tree_find int_or_awaits _ (fun trees => (forall pos pnat3 pin3 path_tl,
        partial_valid_list_def_tree' (length eqns_hd) (length vars_hd + 1) v trees pos (pnat1 ++ pnat2 :: pnat3)
          (eqns_hd ++ (vars_hd ++ Index (Var v) (pin1 ++ pin2 :: pin3 ++ path_tl) :: vars_tl, expr) :: eqns_tl) ->
        partial_valid_list_def_tree' (length eqns_hd) (length vars_hd) v trees pos (pnat1 ++ pnat2 :: pnat3) (eqns_hd ++ (vars_hd ++ Index (Var v) (pin1 ++ pin2 :: pin3 ++ path_tl) :: vars_tl, expr) :: eqns_tl)
        ) : Prop) _ _ _ _); simpl.
    {
        move=> [eq_num|typ] pnat3 pin3 path_tl.
        {
            move=> [Hinf_eq H].
            split; trivial.
            move=> pos l' HInf top_eq.
            apply (H _ l') in HInf; trivial; clear H.
            case_eq (pos =? length eqns_hd); move=> H; rewrite H in HInf; trivial.
            rewrite Nat.eqb_eq in H; symmetry in H; destruct H.
            rewrite HInf; clear HInf.
            unfold partial_defined_in; rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl; split.
            all: move=> [vL [e [ind [HEq [is_spec' [i [HInf HIn]]]]]]].
            all: exists vL; exists e; exists ind; repeat split; trivial.
            all: exists i; split; auto.
            {
                rewrite <-ltnS in HInf.
                rewrite addn1 in HInf; apply ltnW in HInf; auto.
            }
            {
                rewrite addn1.
                destruct (leq_Cases _ _ HInf) as [HEq'|]; trivial.
                rewrite <- HEq' in HIn.
                exfalso; move: HIn.
                inversion HEq.
                rewrite nth_error_app2; trivial; rewrite Nat.sub_diag; simpl.
                move=> H; destruct H as [H|[H _]]; move: is_spec'; inversion H.
                move=> is_spec'.
                apply not_spec.
                move: is_spec is_spec' top_eq; clear.
                move: pin1 pnat1; induction l' as [|hd tl HRec]; move=> [|pin_hd pin1].
                all: move=> pnat1 H; inversion H as [|h1 h2 t1 t2 rel_hd1 rel_tl1]; simpl.
                all: move=> H'; inversion H' as [|hd1 hd2 td1 td2 rel_hd2 rel_tl2].
                by move=> LEq; move: rel_hd2; inversion LEq as [| |hd1' hd2' td1' td2' ->]; trivial.
                move=> top_eq; apply (HRec pin1 t1); trivial.
                inversion top_eq; assumption.
            }
        }
        {
            move=> [H H']; split; trivial.
            clear H'.
            move=> l' top_eq partial_def; apply (H l'); clear H; trivial.
            move: partial_def.
            unfold partial_defined_in.
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            move=> [vL [e [ind [HEq [is_spec' [i [HInf H]]]]]]].
            exists vL; exists e; exists ind; split; trivial.
            split; trivial; exists i.
            rewrite addn1.
            destruct (leq_Cases _ _ HInf) as [HEq'|]; auto.
            destruct HEq'.
            exfalso; apply not_spec; move: H is_spec is_spec' top_eq; inversion HEq.
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            move=> [H|[H _]]; inversion H; clear.
            move: pin1 pnat1; induction l' as [|hd tl HRec]; move=> [|pin_hd pin1].
            all: move=> pnat1 H; inversion H as [|h1 h2 t1 t2 rel_hd1 rel_tl1]; simpl.
            all: move=> H'; inversion H' as [|hd1 hd2 td1 td2 rel_hd2 rel_tl2].
            by move=> LEq; move: rel_hd2; inversion LEq as [| |hd1' hd2' td1' td2' ->]; trivial.
            move=> top_eq; apply (HRec pin1 t1); trivial.
            inversion top_eq; assumption.
        }
    }
    {
        move=> trees HRec pnat3 pin3 path_tl [not_partial_defined [not_defined partial_def]].
        repeat split.
        {
            move: not_spec is_spec not_partial_defined; clear.
            unfold partial_defined_in.
            rewrite nth_error_app2; auto.
            rewrite Nat.sub_diag; simpl.
            move=> not_spec is_spec not_partial_defined [vL [e [ind [HEq [is_spec' [i [HInf HEq']]]]]]].
            apply not_partial_defined; clear not_partial_defined.
            move: HEq' is_spec'.
            inversion HEq; clear H0 H1 HEq.
            destruct (leq_Cases _ _ HInf) as [<-|HInf']; clear HInf.
            {
                rewrite nth_error_app2; trivial.
                rewrite Nat.sub_diag; simpl.
                move=> [H|[H _]]; inversion H.
                intro; exfalso; apply not_spec.
                destruct (list_rel_append is_specialization pnat1 pin1 (pnat2 :: pnat3) (pin2 :: pin3 ++ path_tl)) as [[_ Abs] _].
                by split; [> assumption | exact (list_rel_length _ _ _ is_spec) ].
                inversion Abs; assumption.
            }
            {
                rewrite addn1.
                move=> HEq is_spec'.
                do 3 eexists; repeat split.
                by exact is_spec'.
                eexists; split.
                by exact HInf'.
                trivial.
            }
        }
        {
            trivial.
        }
        {
            specialize HRec with 0 pnat3 pin3 path_tl.
            simpl in HRec; apply HRec; trivial.
        }
    }
    {
        trivial.
    }
    {
        move=> hd HRec_hd tl HRec_tl pos path_nat path_in path_tl [partial_valid_hd partial_valid_tl].
        split.
        {
            rewrite <-app_assoc in partial_valid_hd.
            rewrite <-app_assoc; simpl in *.
            apply HRec_hd; trivial.
        }
        {
            apply HRec_tl; trivial.
        }
    }
Qed.

Lemma update_def_tree_valid:
    forall len_eqns_hd tree path_tl tree',
        update_def_tree path_tl len_eqns_hd tree = Some tree' ->
        valid_dtree_access tree' path_tl.
Proof.
    move=> len_eqns_hd.
    refine (def_tree_find _ _ (fun trees => (forall pos path_tl indices trees',
        update_def_trees pos path_tl len_eqns_hd (trees) indices = Some trees' ->
        valid_dtrees_access trees' pos indices path_tl /\
        indices <> nil /\
        Forall (fun i => i < pos + dtrees_length trees') indices) : Prop) _ _ _ _); simpl.
    {
        move=> [eq_num|typ].
        by idtac.
        move=> path_tl tree' HEq.
        apply build_def_tree_from_type_access in HEq; trivial.
    }
    {
        move=> trees HRec [|path_hd path_tl] tree'.
        by idtac.
        move: (HRec 0 path_tl); clear HRec.
        simpl; move=> HRec.
        destruct path_hd as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i eval_eq | by idtac].
            move: (HRec [:: i]); clear HRec; move=> HRec.
            destruct update_def_trees as [trees'|]; [> idtac | by idtac ].
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            move: (HRec trees'); clear HRec; impl_tac; trivial.
            rewrite eval_eq; rewrite add0n.
            move=> [H1 [not_empty H2]]; split; [> assumption | split; assumption].
        }
        {
            by idtac.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            move: (HRec iL); clear HRec; move=> HRec.
            destruct update_def_trees as [trees'|].
            2: by idtac.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            move: (HRec trees'); clear HRec; impl_tac; trivial.
            rewrite HEq; rewrite add0n.
            move=> [H1 [not_empty H2]]; split; [> assumption | split; assumption].
        }
    }
    {
        move=> pos path_tl indices trees'.
        case_eq (forallb (Nat.ltb^~ pos) indices && List.existsb xpredT indices); move=> all_inf HEq.
        all: inversion HEq as [H]; clear HEq H; simpl; trivial; auto.
        split; trivial.
        move/andP in all_inf; destruct all_inf as [all_inf not_empty].
        split.
        {
            move=> H; rewrite H in not_empty; simpl in not_empty.
            discriminate not_empty.
        }
        {
            move: all_inf; unfold is_true.
            rewrite List.forallb_forall; rewrite List.Forall_forall.
            move=> H x LIn; apply H in LIn; move: LIn.
            rewrite Nat.ltb_lt; move/ltP; rewrite addn0; trivial.
        }
    }
    {
        move=> hd HRec_hd tl HRec_tl pos path_tl indices trees'.
        move: (HRec_tl (pos + 1) path_tl indices); clear HRec_tl.
        destruct update_def_trees as [trees'1|]; [> simpl | by idtac ].
        move=> HRec_tl HEq; specialize HRec_tl with trees'1.
        move: HRec_tl; impl_tac; trivial.
        rewrite addn1; rewrite addSn; move=> [].
        case_eq (List.existsb (Nat.eqb pos) indices); move=> Hmem; rewrite Hmem in HEq.
        2: by inversion HEq as [H']; clear H' HEq trees'; simpl; rewrite Hmem; rewrite add1n; rewrite addnS.
        case_eq (update_def_tree path_tl len_eqns_hd hd).
        2: by move=> H; rewrite H in HEq; discriminate.
        move=> hd' update_eq; rewrite update_eq in HEq.
        inversion HEq as [H']; clear H' HEq trees'; simpl.
        rewrite Hmem; move=> H [a b]; rewrite add1n; rewrite addnS; repeat split; auto.
    }
Qed.

Lemma update_def_tree_subtree:
    forall len_eqns_hd tree path_tl tree',
        update_def_tree path_tl len_eqns_hd tree = Some tree' ->
        sub_dtree tree tree'.
Proof.
    move=> len_eqns_hd.
    refine (def_tree_find _ _ (fun trees => (forall pos path_tl indices trees',
        update_def_trees pos path_tl len_eqns_hd trees indices = Some trees' ->
        sub_dtrees trees trees') : Prop) _ _ _ _); simpl.
    {
        move=> [eq_num|typ].
        by idtac.
        by intros; constructor.
    }
    {
        move=> trees HRec [|path_hd path_tl] tree'.
        by idtac.
        move: (HRec 0 path_tl); clear HRec; move=> HRec.
        destruct path_hd as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i eval_eq | by idtac].
            move: (HRec [:: i]); clear HRec; move=> HRec.
            destruct update_def_trees as [trees'|].
            2: by idtac.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            constructor; apply HRec; reflexivity.
        }
        {
            by idtac.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            move: (HRec iL); clear HRec; move=> HRec.
            destruct update_def_trees as [trees'|].
            2: by idtac.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            constructor; apply HRec; reflexivity.
        }
    }
    {
        move=> pos path_tl indices trees'.
        case_eq (forallb (Nat.ltb^~ pos) indices && List.existsb xpredT indices); move=> all_inf HEq.
        all: inversion HEq as [H]; clear HEq H; simpl; trivial; auto.
        by constructor.
    }
    {
        move=> hd HRec_hd tl HRec_tl pos path_tl indices trees'.
        move: (HRec_tl (pos + 1) path_tl indices); clear HRec_tl.
        destruct update_def_trees as [trees'1|]; [> simpl | by idtac ].
        move=> HRec_tl HEq; specialize HRec_tl with trees'1.
        move: HRec_tl; impl_tac; trivial.
        case_eq (List.existsb (Nat.eqb pos) indices); move=> Hmem; rewrite Hmem in HEq.
        2: by inversion HEq as [H']; clear H' HEq trees'; intro; constructor; trivial; apply sub_dtree_refl.
        case_eq (update_def_tree path_tl len_eqns_hd hd).
        2: by move=> H; rewrite H in HEq; discriminate.
        move=> hd' update_eq; rewrite update_eq in HEq.
        inversion HEq as [H']; clear H' HEq trees'.
        intro; constructor; trivial.
        apply HRec_hd in update_eq; trivial.
    }
Qed.

Lemma update_def_tree_type_soundness:
    forall len_eqns_hd tree path_tl tree' typ,
        update_def_tree path_tl len_eqns_hd tree = Some tree' ->
        def_tree_of_type tree typ ->
            def_tree_of_type tree' typ.
Proof.
    move=> len_eqns_hd.
    refine (def_tree_find _ _ (fun trees => (forall pos path_tl indices trees' typ,
        update_def_trees pos path_tl len_eqns_hd (trees) indices = Some trees' ->
        list_def_tree_of_type trees typ (dtrees_length trees) ->
        dtrees_length trees = dtrees_length trees' /\
        list_def_tree_of_type trees' typ (dtrees_length trees')) : Prop) _ _ _ _); simpl.
    {
        move=> [eq_num|typ].
        by idtac.
        move=> path_tl tree' typ' HEq H; destruct H.
        apply build_def_tree_from_type_type_soundness in HEq; assumption.
    }
    {
        move=> trees HRec [|path_hd path_tl] tree' typ.
        by idtac.
        move: (HRec 0 path_tl); clear HRec.
        simpl; move=> HRec.
        destruct path_hd as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i eval_eq | by idtac].
            move: (HRec [:: i]); clear HRec; move=> HRec.
            destruct update_def_trees as [trees'|].
            2: by move=> H; inversion H.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            destruct typ as [| |typ len].
            1,2: move=> [].
            move=> type_of_trees.
            specialize HRec with trees' typ; move: HRec.
            impl_tac; trivial.
            impl_tac.
            by rewrite (list_def_tree_of_type_length _ _ _ type_of_trees); assumption.
            rewrite (list_def_tree_of_type_length _ _ _ type_of_trees).
            move=> [-> H]; assumption.
        }
        {
            by idtac.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            move: (HRec iL); clear HRec; move=> HRec.
            destruct update_def_trees as [trees'|].
            2: by idtac.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            destruct typ as [| |typ len].
            1,2: by move=> [].
            move=> type_of_trees.
            specialize HRec with trees' typ; move: HRec.
            impl_tac; trivial.
            impl_tac.
            by rewrite (list_def_tree_of_type_length _ _ _ type_of_trees); assumption.
            rewrite (list_def_tree_of_type_length _ _ _ type_of_trees).
            move=> [-> H]; assumption.
        }
    }
    {
        move=> pos path_tl indices trees' typ.
        case_eq (forallb (Nat.ltb^~ pos) indices && List.existsb xpredT indices); move=> all_inf HEq.
        all: inversion HEq as [H]; clear HEq H; simpl; split; trivial.
    }
    {
        move=> hd HRec_hd tl HRec_tl pos path_tl indices trees' typ.
        move: (HRec_tl (pos + 1) path_tl indices); clear HRec_tl.
        destruct update_def_trees as [trees'1|]; [> simpl | by idtac ].
        move=> HRec_tl HEq [typ_hd typ_tl]; specialize HRec_tl with trees'1 typ.
        move: HRec_tl; impl_tac; trivial.
        impl_tac; trivial.
        move=> [length_eq_tl typ_tl'].
        destruct List.existsb.
        2: by inversion HEq as [H']; clear H' HEq trees'; simpl; auto.
        case_eq (update_def_tree path_tl len_eqns_hd hd).
        2: by move=> H; rewrite H in HEq; discriminate.
        move=> hd' update_eq; rewrite update_eq in HEq.
        inversion HEq as [H']; clear H' HEq trees'; simpl; split; [> auto | split; trivial].
        apply (HRec_hd _ _ typ) in update_eq; assumption.
    }
Qed.

Lemma update_def_tree_soundness:
    forall eqns_hd tree path_tl tree',
        update_def_tree path_tl (length eqns_hd) tree = Some tree' ->
            forall eqns_tl vars_hd vars_tl expr v path_nat path_in,
            (partial_valid_def_tree' (length eqns_hd) (length vars_hd + 1) v tree path_nat (eqns_hd ++ (vars_hd ++ Index (Var v) (path_in ++ path_tl) :: vars_tl, expr) :: eqns_tl) ->
            list_rel is_specialization path_nat path_in ->
            partial_valid_def_tree' (length eqns_hd) (length vars_hd) v tree' path_nat (eqns_hd ++ (vars_hd ++ Index (Var v) (path_in ++ path_tl) :: vars_tl, expr) :: eqns_tl)).
Proof.
    move=> eqns_hd.
    refine (def_tree_find _ _ (fun trees => (forall ind pos path_tl indices trees',
        update_def_trees pos path_tl (length eqns_hd) (trees) indices = Some trees' ->
        forall eqns_tl vars_hd vars_tl expr v path_in path_nat,
            (partial_valid_list_def_tree' (length eqns_hd) (length vars_hd + 1) v trees pos path_nat
            (eqns_hd ++ (vars_hd ++ Index (Var v) (path_in ++ ind:: path_tl) :: vars_tl, expr) :: eqns_tl) ->
            length path_nat = length path_in ->
            list_rel is_specialization path_nat path_in ->
            (forall i, List.existsb (Nat.eqb i) indices <-> is_specialization i ind) ->
            partial_valid_list_def_tree' (length eqns_hd) (length vars_hd) v trees' pos path_nat (eqns_hd ++ (vars_hd ++ Index (Var v) (path_in ++ ind :: path_tl) :: vars_tl, expr) :: eqns_tl)
            )) : Prop) _ _ _ _); simpl.
    {
        move=> [eq_num|typ].
        by idtac.
        move=> path_tl tree' HEq.
        move=> eqns_tl vars_hd vars_tl expr v path_nat path_in [partial_def def] is_spec.
        apply (build_def_tree_from_type_soundness _ _ _ _ HEq); assumption.
    }
    {
        move=> trees HRec [|path_hd path_tl] tree'.
        by idtac.
        move: (HRec path_hd 0 path_tl); clear HRec.
        simpl; move=> HRec.
        destruct path_hd as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i eval_eq | by idtac].
            move: (HRec [:: i]); clear HRec; move=> HRec.
            destruct update_def_trees as [trees'|].
            2: by idtac.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            move: (HRec trees'); clear HRec; impl_tac; trivial.
            move=> HRec.
            move=> eqns_tl vars_hd vars_tl expr v path_nat path_in.
            move=> [never_partial_defined [never_defined partial_valid]] is_spec.
            apply HRec in partial_valid; simpl; auto.
            {
                repeat split; trivial.
                move: is_spec never_partial_defined; clear.
                unfold partial_defined_in.
                rewrite nth_error_app2; auto.
                rewrite Nat.sub_diag; simpl.
                move=> is_spec_raw not_partial_defined [vL [e' [ind [HEq [is_spec [i [HInf HEq']]]]]]].
                apply not_partial_defined; clear not_partial_defined.
                do 3 eexists; repeat split.
                by exact is_spec.
                move: HInf HEq' is_spec is_spec_raw; inversion HEq; clear.
                move=> HInf.
                destruct (leq_Cases _ _ HInf) as [HEq|HInf'].
                {
                    destruct HEq.
                    rewrite nth_error_app2; trivial; rewrite Nat.sub_diag; simpl.
                    move=> H lrel1 lrel2.
                    apply list_rel_length in lrel1.
                    apply list_rel_length in lrel2.
                    rewrite lrel2 in lrel1; exfalso; move: lrel1.
                    destruct H as [H'|[H' _]]; inversion H'.
                    rewrite app_length; simpl.
                    clear.
                    induction (length path_in) as [|l HRec]; simpl.
                    by idtac.
                    move=> H; apply HRec; inversion H as [H'].
                    do 2 rewrite <- H'; reflexivity.
                }
                rewrite addn1.
                move=> H _ _; exists i; split; trivial.
            }
            {
                apply list_rel_length in is_spec; assumption.
            }
            {
                move=> i'; rewrite orb_false_r.
                unfold is_true; rewrite Nat.eqb_eq.
                split; move=> H.
                {
                    destruct H.
                    constructor; assumption.
                }
                {
                    inversion H as [ae' i2 eval_eq'| |].
                    rewrite eval_eq in eval_eq'.
                    inversion eval_eq'; reflexivity.
                }
            }
        }
        {
            by idtac.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            move: (HRec iL); clear HRec; move=> HRec.
            destruct update_def_trees as [trees'|].
            2: by idtac.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            move: (HRec trees'); clear HRec; impl_tac; trivial; move=> HRec.
            move=> eqns_tl vars_hd vars_tl expr v path_nat path_in.
            move=> [never_partial_defined [never_defined partial_valid]] is_spec.
            apply HRec in partial_valid; simpl; auto.
            {
                repeat split; trivial.
                move: is_spec never_partial_defined; clear.
                unfold partial_defined_in.
                rewrite nth_error_app2; auto.
                rewrite Nat.sub_diag; simpl.
                move=> is_spec_raw not_partial_defined [vL [e' [ind [HEq [is_spec [i [HInf HEq']]]]]]].
                apply not_partial_defined; clear not_partial_defined.
                do 3 eexists; repeat split.
                by exact is_spec.
                move: HInf HEq' is_spec is_spec_raw; inversion HEq; clear.
                move=> HInf.
                destruct (leq_Cases _ _ HInf) as [HEq|HInf'].
                {
                    destruct HEq.
                    rewrite nth_error_app2; trivial; rewrite Nat.sub_diag; simpl.
                    move=> H lrel1 lrel2.
                    apply list_rel_length in lrel1.
                    apply list_rel_length in lrel2.
                    rewrite lrel2 in lrel1; exfalso; move: lrel1.
                    destruct H as [H'|[H' _]]; inversion H'.
                    rewrite app_length; simpl.
                    clear.
                    induction (length path_in) as [|l HRec]; simpl.
                    by idtac.
                    move=> H; apply HRec; inversion H as [H'].
                    do 2 rewrite <- H'; reflexivity.
                }
                rewrite addn1.
                move=> H _ _; exists i; split; trivial.
            }
            {
                apply list_rel_length in is_spec; assumption.
            }
            {
                move=> pos; split; move=> Hmem.
                {
                    assert (exists ae, List.In ae aeL /\ eval_arith_expr nil ae = Some pos) as HIn.
                    {
                        move: HEq Hmem; clear; move: iL.
                        induction aeL as [|hd tl HRec]; simpl.
                        {
                            move=> iL H; inversion H.
                            by simpl.
                        }
                        {
                            move=> iL.
                            destruct fold_right as [l|].
                            2: by idtac.
                            specialize HRec with l.
                            case_eq (eval_arith_expr nil hd); [> move=> i HEq | by idtac].
                            move=> H; inversion H as [H']; clear H H' iL; simpl.
                            move :(orb_prop_elim (pos =? i) (List.existsb (Nat.eqb pos) l)).
                            move=> H_or H; rewrite H in H_or; clear H.
                            move: H_or; impl_tac; simpl; trivial.
                            move=> [H|H]; apply Is_true_eq_true in H.
                            {
                                rewrite Nat.eqb_eq in H; destruct H.
                                exists hd; auto.
                            }
                            destruct HRec as [ae [HIn eval_eq]]; trivial.
                            exists ae; auto.
                        }
                    }
                    destruct HIn as [ae [HIn eval_eq]].
                    apply (SpecSlice ae); trivial.
                }
                {
                    inversion Hmem as [|ae aeL' i HIn eval_eq'|].
                    move: HIn eval_eq' HEq; clear.
                    move: iL; induction aeL as [|hd tl HRec]; simpl.
                    by idtac.
                    move=> iL [->|HIn].
                    {
                        move=> ->; destruct fold_right.
                        2: by idtac.
                        move=> H; inversion H; simpl.
                        rewrite Nat.eqb_refl; auto.
                    }
                    {
                        move=> eval_eq; destruct fold_right as [l|].
                        2: by idtac.
                        destruct (eval_arith_expr nil hd).
                        2: by idtac.
                        move=> H; inversion H; simpl.
                        rewrite HRec; trivial.
                        unfold is_true.
                        rewrite orb_true_iff; auto.
                    }
                }
            }
        }
    }
    {
        move=> ind pos path_tl indices trees'.
        case_eq (forallb (Nat.ltb^~ pos) indices && List.existsb xpredT indices); move=> all_inf HEq.
        all: inversion HEq as [H]; clear HEq H; simpl; trivial; auto.
    }
    {
        move=> hd HRec_hd tl HRec_tl ind pos path_tl indices trees'.
        move: (HRec_tl ind (pos + 1) path_tl indices); clear HRec_tl.
        destruct update_def_trees as [trees'1|]; [> simpl | by idtac ].
        move=> HRec_tl HEq.
        move: (HRec_tl trees'1); clear HRec_tl; impl_tac; trivial.
        move=> HRec_tl eqns_tl vars_hd vars_tl expr v path_in path_nat.
        move=> [pvalid_hd pvalid_tl] length_eq spec_front is_spec.
        specialize HRec_tl with eqns_tl vars_hd vars_tl expr v path_in path_nat.
        rewrite addn1 in HRec_tl.
        rewrite addn1 in pvalid_tl; rewrite addn1 in HRec_tl.
        apply HRec_tl in pvalid_tl; trivial; clear HRec_tl.
        move: HEq.
        case_eq (List.existsb (Nat.eqb pos) indices).
        {
            move=> HEq_exists.
            case_eq (update_def_tree path_tl (length eqns_hd) hd); [> move=> tree' HEq | by idtac].
            move=> H; inversion H as [H']; simpl; split; trivial.
            clear H H' trees'.
            move: (HRec_hd _ _ HEq); clear HRec_hd; move=> HRec_hd.
            specialize HRec_hd with eqns_tl vars_hd vars_tl expr v (path_nat ++ [:: pos]) (path_in ++ [:: ind]).
            rewrite <- app_assoc in HRec_hd; simpl in HRec_hd.
            apply HRec_hd; trivial.
            rewrite list_rel_last; split; trivial.
            apply is_spec; auto.
        }
        {
            move=> exists_false H; inversion H; simpl; split; auto.
            move: (partial_valid_def_tree'_decr eqns_hd eqns_tl vars_hd vars_tl expr v hd path_nat pos nil path_in ind nil path_tl); simpl.
            impl_tac; trivial.
            impl_tac; trivial.
            impl_tac.
            {
                rewrite <-is_spec.
                rewrite exists_false.
                by idtac.
            }
            trivial.
        }
    }
Qed.

Lemma partial_valid_dtree_change_name:
    forall eqns_hd eqns_tl var ident expr vars_hd vars_tl path_in tree,
        get_ident var <> ident ->
        partial_valid_def_tree' (length eqns_hd) (length vars_hd).+1 ident tree path_in (eqns_hd ++ (vars_hd ++ var :: vars_tl, expr) :: eqns_tl) ->
        partial_valid_def_tree' (length eqns_hd) (length vars_hd) ident tree path_in (eqns_hd ++ (vars_hd ++ var :: vars_tl, expr) :: eqns_tl).
Proof.
    move=> eqns_hd eqns_tl var ident expr vars_hd vars_tl path_in tree ident_diff.
    move: tree path_in.
    refine (def_tree_find _ _ (fun trees => forall pos path_in,
        partial_valid_list_def_tree' (length eqns_hd) (length vars_hd).+1 ident trees pos path_in (eqns_hd ++ (vars_hd ++ var :: vars_tl, expr) :: eqns_tl) ->
        partial_valid_list_def_tree' (length eqns_hd) (length vars_hd) ident trees pos path_in (eqns_hd ++ (vars_hd ++ var :: vars_tl, expr) :: eqns_tl)
        ) _ _ _ _).
    {
        move=> [eq_num|typ] path_in; simpl.
        {
            move=> [HInf_eq_num H].
            split; trivial.
            move=> pos l' HInf top_eq; rewrite H; clear H; trivial.
            case_eq (pos =? length eqns_hd).
            2: by idtac.
            rewrite Nat.eqb_eq; move=> ->.
            unfold partial_defined_in; rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            clear HInf.
            split; move=> [vL [e [ind [HEq [is_spec [i [HInf HEq']]]]]]].
            {
                do 3 eexists; repeat split.
                by exact is_spec.
                move: HEq'; inversion HEq; move=> HEq'.
                exists i; split; trivial.
                apply ltnW in HInf; assumption.
            }
            {
                do 3 eexists; repeat split.
                by exact is_spec.
                move: HEq'; inversion HEq; move=> HEq'.
                exists i; split; trivial.
                destruct (leq_Cases _ _ HInf) as [Eq|]; trivial.
                destruct Eq.
                rewrite nth_error_app2 in HEq'; trivial.
                rewrite Nat.sub_diag in HEq'; simpl in HEq'.
                exfalso; apply ident_diff.
                destruct HEq' as [H|[H _]]; inversion H; simpl; reflexivity.
            }
        }
        {
            move=> [H1 H2]; split; trivial; clear H2.
            move=> l' top_eq partial_def; apply (H1 l'); clear H1; trivial.
            move: partial_def.
            unfold partial_defined_in; rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            move=> [vL [e [ind [HEq [is_spec [i [HInf HEq']]]]]]].
            do 3 eexists; repeat split.
            by exact is_spec.
            move: HEq'; inversion HEq; move=> HEq'.
            exists i; split; trivial.
            destruct (leq_Cases _ _ HInf) as [Eq|]; trivial.
            destruct Eq.
            rewrite nth_error_app2 in HEq'; trivial.
            rewrite Nat.sub_diag in HEq'; simpl in HEq'.
            destruct HEq' as [H|[H _]]; exfalso; apply ident_diff.
            all: inversion H; simpl; reflexivity.
        }
    }
    {
        simpl.
        move=> trees HRec path_in [not_partial_def [not_def partial_valid]].
        repeat split; trivial.
        {
            clear HRec partial_valid not_def.
            move=> partial_def; apply not_partial_def; clear not_partial_def.
            move: partial_def.
            unfold partial_defined_in; rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            move=> [vL [e [ind [HEq [is_spec [i [HInf HEq']]]]]]].
            do 3 eexists; repeat split.
            by exact is_spec.
            move: HEq'; inversion HEq; move=> HEq'.
            exists i; split; trivial.
            destruct (leq_Cases _ _ HInf) as [Eq|]; trivial.
            destruct Eq.
            rewrite nth_error_app2 in HEq'; trivial.
            rewrite Nat.sub_diag in HEq'; simpl in HEq'.
            destruct HEq' as [H|[H _]]; exfalso; apply ident_diff.
            all: inversion H; simpl; reflexivity.
        }
        {
            apply HRec; trivial.
        }
    }
    {
        simpl; trivial.
    }
    {
        simpl.
        move=> tree HRec_hd trees HRec_tl pos path_in [valid_hd valid_tl].
        split; auto.
    }
Qed.

Lemma valid_access_keep_lemma_dtree:
    forall ind typ path trees pos,
        valid_dtrees_access trees pos ind path ->
        list_def_tree_of_type trees typ (dtrees_length trees) ->
        (exists i, List.In i ind /\ i >= pos /\ i < pos + dtrees_length trees) ->
        exists t,
            valid_dtree_access t path /\ def_tree_of_type t typ.
Proof.
    move=> ind typ path trees.
    induction trees as [|hd tl HRec]; simpl.
    {
        move=> pos _ _ [i [_ [HInf HSup]]].
        rewrite addn0 in HSup.
        move: HSup; move/ltP; rewrite <-Nat.nle_gt; move/leP.
        move/negP.
        move=> H; destruct (H HInf).
    }
    {
        move=> pos valid_acc type_of [i [LIn [HInf HSup]]].
        specialize HRec with pos.+1.
        case_eq (List.existsb (Nat.eqb pos) ind).
        {
            move=> H; rewrite H in valid_acc.
            destruct type_of; destruct valid_acc.
            exists hd; split; assumption.
        }
        {
            destruct (leq_Cases _ _ HInf) as [->|H].
            {
                rewrite <-not_true_iff_false; rewrite List.existsb_exists.
                move=> H; exfalso; apply H.
                exists i; rewrite Nat.eqb_refl; auto.
            }
            {
                move=> HEq; rewrite HEq in valid_acc.
                destruct valid_acc; destruct type_of.
                apply HRec; trivial.
                exists i; split; [> assumption | split; [> trivial | idtac ]].
                rewrite add1n in HSup; rewrite addnS in HSup.
                rewrite addSn; assumption.
            }
        }
    }
Qed.

Lemma valid_access_keep_dtree:
    forall ind tree typ,
        valid_dtree_access tree ind ->
        def_tree_of_type tree typ ->
        valid_access typ ind.
Proof.
    move=> ind; induction ind as [|ind tl HRec].
    {
        move=> tree [|d m|typ len]; simpl; trivial.
    }
    {
        move=> [b|trees] typ; simpl.
        by move=> H; inversion H.
        destruct typ as [| |typ len].
        1,2: by move=> _ [].
        simpl; destruct ind as [ae|ae1 ae2|aeL].
        {
            unfold eval_lt.
            destruct eval_arith_expr.
            2: by move=> [].
            move=> [H0 [H1 H2]] trees_of_type.
            inversion H1; rewrite <-(list_def_tree_of_type_length _ _ _ trees_of_type).
            split; trivial.
            destruct (valid_access_keep_lemma_dtree [:: n] typ tl trees 0) as [t [valid of_type]].
            by assumption.
            by rewrite (list_def_tree_of_type_length _ _ _ trees_of_type); assumption.
            by exists n; simpl; auto.
            by exact (HRec _ _ valid of_type).
        }
        {
            unfold eval_lt.
            destruct eval_arith_expr.
            2: by move=> [].
            destruct eval_arith_expr.
            2: by move=> [].
            move=> [H0 [H1 H2]] trees_of_type.
            rewrite Forall_forall in H1.
            rewrite <-(list_def_tree_of_type_length _ _ _ trees_of_type).
            split.
            {
                destruct (valid_access_keep_lemma_dtree _ typ _ _ _ H2) as [t [valid of_type]].
                by rewrite (list_def_tree_of_type_length _ _ _ trees_of_type); assumption.
                {
                    eexists; split.
                    apply gen_range_in_l.
                    split; trivial.
                    rewrite add0n; apply H1.
                    apply gen_range_in_l.
                }
                by exact (HRec _ _ valid of_type).
            }
            {
                split; apply H1; [> refine (gen_range_in_l _ _) | refine (gen_range_in_r _ _)].
            }
        }
        {
            case_eq (fold_right (fun ae l => l' <- l; i <- eval_arith_expr nil ae; Some (i :: l')) (Some nil) aeL).
            2: move=> _ [].
            move=> iL HEq [NotEmpty [AllInf valid_acc]] type_of; split; [> idtac | split].
            {
                destruct (valid_access_keep_lemma_dtree _ typ _ _ _ valid_acc) as [t [valid of_type]].
                by rewrite (list_def_tree_of_type_length _ _ _ type_of); assumption.
                {
                    destruct iL as [|i iL].
                    by destruct (NotEmpty Logic.eq_refl).
                    exists i; simpl; split; [> left; reflexivity | split; trivial ].
                    rewrite add0n; inversion AllInf.
                    assumption.
                }
                by exact (HRec _ _ valid of_type).
            }
            {
                rewrite <-(list_def_tree_of_type_length _ _ _ type_of).
                move: HEq AllInf; clear; move: iL.
                induction aeL as [|ae aeL HRec]; simpl.
                intros; constructor.
                destruct fold_right.
                2: move=> iL H; inversion H.
                case_eq (eval_arith_expr nil ae).
                2: move=> _ iL H; inversion H.
                move=> i HEq iL H; inversion H as [H']; clear H H' iL.
                move=> H'; inversion H'.
                constructor.
                {
                    unfold eval_lt; rewrite HEq; assumption.
                }
                {
                    apply (HRec _ Logic.eq_refl); trivial.
                }
            }
            {
                move=> H; rewrite H in HEq; apply NotEmpty; simpl in HEq; inversion HEq; reflexivity.
            }
        }
    }
Qed.

Lemma partial_valid_def_tree_add_prim:
    forall eqns_hd eqns_tl vars expr v t path,
        partial_valid_def_tree (length eqns_hd).+1 v t path (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_def_tree' (length eqns_hd) (length vars).+1 v t path (eqns_hd ++ (vars, expr) :: eqns_tl).
Proof.
    move=> eqns_hd eqns_tl vars expr v.
    refine (def_tree_find _ _ (fun trees => forall path pos,
        partial_valid_list_def_tree (length eqns_hd).+1 v trees pos path (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_list_def_tree' (length eqns_hd) (length vars).+1 v trees pos path (eqns_hd ++ (vars, expr) :: eqns_tl)
    ) _ _ _ _).
    {
        move=> [eq_num|typ] path; simpl.
        {
            move=> [HSInf Hdefined].
            split.
            by apply ltnW.
            move=> pos l' HInf top_eq.
            destruct (leq_Cases _ _ HInf) as [HEq|HInf'].
            {
                destruct HEq; rewrite Nat.eqb_refl.
                split.
                {
                    move=> [H <-]; rewrite <-H in HSInf.
                    clear top_eq l'.
                    exfalso; apply (Nat.nle_succ_diag_l (length eqns_hd)).
                    apply/leP; assumption.
                }
                {
                    clear.
                    unfold partial_defined_in.
                    rewrite nth_error_app2; trivial.
                    rewrite Nat.sub_diag; simpl.
                    move=> [vL [e [ind [HEq [is_spec [i [HInf HEq']]]]]]].
                    move: HInf HEq'; inversion HEq.
                    move=> HInf.
                    destruct (nth_error_None vL i) as [_ ->].
                    by move=> [Abs|[Abs _]].
                    apply ltnW in HInf.
                    apply/leP; trivial.
                }
            }
            {
                rewrite Hdefined; trivial.
                case_eq (pos =? length eqns_hd).
                2: by split.
                rewrite Nat.eqb_eq; move=> HEq; destruct HEq.
                exfalso; apply (Nat.nle_succ_diag_l pos).
                apply/leP; assumption.
            }
        }
        {
            move=> H; split; trivial; clear H.
            move=> l' top_eq.
            unfold partial_defined_in.
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            move=> [vL [e [ind [HEq [is_spec [i [HInf HEq']]]]]]].
            move: HInf HEq'; inversion HEq.
            move=> HInf.
            destruct (nth_error_None vL i) as [_ ->].
            by move=> [Abs|[Abs _]].
            apply ltnW in HInf.
            apply/leP; trivial.
        }
    }
    {
        simpl.
        move=> trees HRec path [defined partial_defined].
        repeat split; auto.
        clear.
        unfold partial_defined_in.
        rewrite nth_error_app2; trivial.
        rewrite Nat.sub_diag; simpl.
        move=> [vL [e [ind [HEq [is_spec [i [HInf HEq']]]]]]].
        move: HInf HEq'; inversion HEq.
        move=> HInf.
        destruct (nth_error_None vL i) as [_ ->].
        by move=> [Abs|[Abs _]].
        apply ltnW in HInf.
        apply/leP; trivial.
    }
    {
        simpl; trivial.
    }
    {
        simpl.
        move=> tree_hd HRec_hd trees HRec_tl path pos [valid_hd valid_tl]; auto.
    }
Qed.

Lemma partial_valid_def_tree_remove_prim:
    forall eqns_hd eqns_tl vars expr v t path,
        partial_valid_def_tree' (length eqns_hd) 0 v t path (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_def_tree (length eqns_hd) v t path (eqns_hd ++ (vars, expr) :: eqns_tl).
Proof.
    move=> eqns_hd eqns_tl vars expr v.
    refine (def_tree_find _ _ (fun trees => forall path pos,
        partial_valid_list_def_tree' (length eqns_hd) 0 v trees pos path (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_list_def_tree (length eqns_hd) v trees pos path (eqns_hd ++ (vars, expr) :: eqns_tl)
    ) _ _ _ _).
    {
        move=> [eq_num|typ] path; simpl.
        {
            move=> [Hinf_eq_num H]; split; trivial.
            move=> pos l' HInf top_eq; apply (H _ l') in HInf; trivial.
            rewrite HInf; clear.
            case_eq (pos =? length eqns_hd).
            2: by split.
            rewrite Nat.eqb_eq; move=> ->.
            unfold partial_defined_in, defined_in.
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            split; move=> [vL [e [ind [HEq [is_spec HIn]]]]].
            all: exists vL; exists e; exists ind; repeat split; trivial.
            {
                destruct HIn as [i [HIn [H|[H ->]]]]; [> left | right; split; trivial].
                all: by apply nth_error_In in H.
            }
            {
                destruct HIn as [H|[H ->]]; apply In_nth_error in H.
                all: destruct H as [i HEq']; exists i; rewrite HEq'; split; auto.
            }
        }
        {
            move=> [partial full] pos l' top_eq HInf.
            destruct (leq_Cases _ _ HInf) as [HEq|HInf'].
            2: apply full; trivial.
            destruct HEq; clear HInf; clear full.
            move=> defined; apply (partial l' top_eq); move: defined.
            unfold partial_defined_in; unfold defined_in.
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            move=> [vL [e [ind [HEq [is_spec HIn]]]]].
            exists vL; exists e; exists ind.
            repeat split; trivial.
            destruct HIn as [H|[H ->]]; apply In_nth_error in H.
            all: destruct H as [i HEq']; exists i; rewrite HEq'; split; auto.
        }
    }
    {
        simpl.
        move=> trees HRec path [not_partial [not_def partial_valid]]; split; auto.
        move=> pos HInf.
        destruct (leq_Cases _ _ HInf) as [HEq|].
        2: apply not_def; trivial.
        destruct HEq.
        move=> defined; apply not_partial; move: defined; clear.
        unfold partial_defined_in; unfold defined_in.
        rewrite nth_error_app2; trivial.
        rewrite Nat.sub_diag; simpl.
        move=> [vL [e [ind [HEq [is_spec HIn]]]]].
        exists vL; exists e; exists ind.
        repeat split; trivial.
        destruct HIn as [H|[H ->]]; apply In_nth_error in H.
        all: destruct H as [i HEq']; exists i; rewrite HEq'; split; auto.
    }
    {
        simpl; trivial.
    }
    {
        simpl.
        move=> tree HRec_hd trees HRec_tl path pos [valid_hd valid_tl]; split; auto.
    }
Qed.

Lemma update_vars_soundness:
    forall tctxt vars vars_hd eqns_hd eqns_tl expr dependancies dependancies',
        update_vars vars (length eqns_hd) dependancies = Some dependancies' ->
        distinct (map fst tctxt) ->
        map fst tctxt = map fst dependancies ->
        list_rel def_tree_of_type (map snd dependancies) (map snd tctxt) ->
        (forall v t, List.In (v, t) dependancies ->
            partial_valid_def_tree' (length eqns_hd) (length vars_hd + length vars + 1) v t nil (eqns_hd ++ ((vars_hd ++ vars, expr) :: eqns_tl))) ->
        Forall (valid_var_dtree dependancies') vars /\
        list_rel sub_dtree (map snd dependancies) (map snd dependancies') /\
        map fst tctxt = map fst dependancies' /\
        list_rel def_tree_of_type (map snd dependancies') (map snd tctxt) /\
        Forall (fun p : ident * def_tree int_or_awaits => let (v, t) := p in
            partial_valid_def_tree' (length eqns_hd) (length vars_hd) v t nil (eqns_hd ++ ((vars_hd ++ vars, expr) :: eqns_tl))) dependancies'.
Proof.
    move=> tctxt vars vars_hd eqns_hd eqns_tl expr; move: vars_hd.
    induction vars as [|v tl HRec]; simpl.
    {
        move=> vars_hd dependancies dependancies' H; inversion H.
        clear.
        move=> Hdistinct fst_eq lrel partial_valid.
        split; [> by constructor | idtac ].
        split.
        {
            clear.
            induction dependancies'; constructor; auto.
            by exact (sub_dtree_refl _).
        }
        split; trivial.
        split; trivial.
        rewrite Forall_forall.
        move=> [v t] HIn; apply partial_valid in HIn.
        move: HIn; clear; rewrite cats0.
        pose (l := @nil nat); fold l; move: t l.
        refine (def_tree_find _ _ (fun trees => forall pos l,
            partial_valid_list_def_tree' (length eqns_hd) (length vars_hd + 1) v trees pos l (eqns_hd ++ (vars_hd, expr) :: eqns_tl) ->
            partial_valid_list_def_tree' (length eqns_hd) (length vars_hd) v trees pos l (eqns_hd ++ (vars_hd, expr) :: eqns_tl)
            ) _ _ _ _).
        {
            move=> [eq_num|typ]; simpl.
            {
                move=> l [HInf_eq_num HEq].
                split; trivial.
                move=> pos l' HInf top_eq; rewrite HEq; auto.
                clear.
                case_eq (pos =? length eqns_hd); [> idtac | by idtac].
                rewrite Nat.eqb_eq; move=> ->.
                rewrite addn1.
                unfold partial_defined_in.
                rewrite nth_error_app2; auto.
                rewrite Nat.sub_diag; simpl.
                split; move=> [vL [e [ind [HEq [is_spec [i [HInf HEq']]]]]]].
                all: exists vL; exists e; exists ind; repeat split; trivial.
                all: exists i; split; trivial.
                {
                    rewrite addn0 in HInf.
                    apply ltnW in HInf; assumption.
                }
                {
                    rewrite addn0.
                    destruct (leq_Cases _ _ HInf) as [Eq|]; trivial.
                    destruct Eq; exfalso; move: HEq'.
                    inversion HEq.
                    clear.
                    destruct (nth_error_None vL (length vL)) as [_ ->].
                    by move=> [|[]].
                    by auto.
                }
            }
            {
                move=> l [H1 H2]; split; trivial; clear H2.
                move=> l' top_eq; specialize H1 with l'.
                move=> partial_def; apply H1; trivial; clear H1; move: partial_def.
                unfold partial_defined_in.
                rewrite nth_error_app2; trivial.
                rewrite Nat.sub_diag; simpl.
                move=> [vL [e [ind [HEq [is_spec [i [HInf HEq']]]]]]].
                do 3 eexists; repeat split.
                by exact is_spec.
                exists i; split.
                {
                    rewrite addn1; rewrite addn0.
                    destruct (leq_Cases _ _ HInf) as [Eq|]; trivial.
                    destruct Eq.
                    exfalso; move: HEq'.
                    inversion HEq.
                    destruct (nth_error_None vL (length vL)) as [_ ->].
                    by move=> [|[]].
                    by idtac.
                }
                {
                    move: HEq'; inversion HEq; trivial.
                }
            }
        }
        {
            simpl.
            move=> trees HRec l [H1 [H2 H3]]; split; auto.
            {
                move=> partial_def; apply H1; move: partial_def; clear.
                unfold partial_defined_in.
                rewrite nth_error_app2; trivial.
                rewrite Nat.sub_diag; simpl.
                move=> [vL [e [ind [HEq [is_spec [i [HInf HEq']]]]]]].
                do 3 eexists; repeat split.
                by exact is_spec.
                exists i; split.
                {
                    rewrite addn1; rewrite addn0.
                    destruct (leq_Cases _ _ HInf) as [Eq|]; trivial.
                    destruct Eq.
                    exfalso; move: HEq'.
                    inversion HEq.
                    destruct (nth_error_None vL (length vL)) as [_ ->].
                    by move=> [|[]].
                    by idtac.
                }
                {
                    move: HEq'; inversion HEq; trivial.
                }
            }
            {
                split; trivial.
                apply HRec.
                rewrite addn0 in H3; trivial.
            }
        }
        {
            trivial.
        }
        {
            simpl.
            move=> tree_hd HRec_hd tree_tl HRec_tl pos l [partial_hd partial_tl].
            split; auto.
            apply HRec_hd; rewrite addn0; trivial.
        }
    }
    {
        move=> vars_hd dependancies dependancies'.
        move: (HRec (vars_hd ++ [:: v])); clear HRec; move=> HRec.
        destruct v as [v|[v|] ind].
        3: by idtac.
        {
            move: (HRec dependancies); clear HRec; move=> HRec.
            destruct update_vars as [dependancies'0|].
            2: by idtac.
            move=> HEq is_map fst_eq type_soundness imp_partial_valid.
            specialize HRec with dependancies'0; move: HRec; impl_tac; trivial.
            impl_tac; trivial.
            impl_tac; trivial.
            impl_tac; trivial.
            impl_tac.
            {
                rewrite app_length; simpl; rewrite Nat.add_1_r.
                rewrite addn1; rewrite addSn.
                rewrite addn1 in imp_partial_valid.
                rewrite addnS in imp_partial_valid.
                rewrite <-app_assoc; simpl; trivial.
            }
            move=> [HEq_map_fst [AllVarValid [fst_eq' [type_soundness' imp_partial_valid']]]].
            move: (update_ctxt_soundness (update_def_tree nil (length eqns_hd)) dependancies'0 v).
            impl_tac.
            {
                rewrite <- fst_eq'; trivial.
            }
            destruct update_ctxt as [ctxt'|].
            2: by idtac.
            move=> H.
            move: (H ctxt'); clear H.
            impl_tac; trivial.
            move=> [find_exists [distinct' [fst_eq'' update_ctxt_soundness]]].
            inversion HEq as [HEq']; destruct HEq'; clear HEq.
            split.
            {
                constructor; simpl.
                {
                    move: fst_eq'' find_exists; clear.
                    move: ctxt'.
                    induction dependancies'0 as [|[key val] tl HRec]; simpl.
                    by move=> c _ H _; apply H; reflexivity.
                    move=> [|[key' val'] tl']; simpl.
                    by discriminate.
                    move=> H; inversion H.
                    by destruct ident_beq; auto.
                }
                {
                    move: fst_eq'' update_ctxt_soundness HEq_map_fst; clear.
                    do 2 rewrite List.Forall_forall.
                    move=> fst_eq H Himp x LIn; apply Himp in LIn.
                    destruct x as [v'|[v'|] ind]; simpl in *.
                    3: by idtac.
                    {
                        move=> find; apply LIn; move: fst_eq find; clear.
                        move: ctxt'.
                        induction dependancies'0 as [|[key val] tl HRec]; simpl; trivial.
                        move=> [|[key' val'] tl']; simpl; [> by idtac | idtac ].
                        move=> H; inversion H.
                        by destruct ident_beq; [> discriminate | apply HRec ].
                    }
                    {
                        move: H LIn; clear.
                        move=> LR; induction LR as [|[k1 v1] [k2 v2] t1 t2 rel_hd rel_tl].
                        all: simpl; auto.
                        simpl in *; destruct rel_hd as [[] H].
                        destruct (ident_beq v'); trivial.
                        destruct ident_beq; [> idtac | by destruct H].
                        move: (update_def_tree_subtree _ _ _ _ H).
                        move=> is_sub valid.
                        exact (sub_dtree_keep_access _ _ _ valid is_sub).
                    }
                }
            }
            split.
            {
                refine (list_rel_trans sub_dtree_trans _ _ _ AllVarValid _).
                move: update_ctxt_soundness; clear; move=> H.
                induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl]; simpl in *.
                all: constructor; trivial.
                destruct H_hd as [_ H_hd]; destruct ident_beq.
                2: by destruct H_hd; exact (sub_dtree_refl _).
                exact (update_def_tree_subtree _ _ _ _ H_hd).
            }
            split.
            by rewrite fst_eq'; apply fst_eq''.
            split.
            {
                move: update_ctxt_soundness type_soundness'; clear.
                move=> H; move: tctxt.
                induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl; trivial.
                move=> [|[k3 v3] t3]; simpl in *.
                by move=> H; inversion H.
                move=> H; inversion H; constructor; auto.
                destruct H_hd as [[] H_hd].
                destruct ident_beq; [> idtac | by destruct H_hd].
                refine (update_def_tree_type_soundness _ _ _ _ _ H_hd _); assumption.
            }
            {
                rewrite Forall_forall.
                move=> [v' t'] HIn.
                apply (list_rel_imp_In_r _ _ update_ctxt_soundness) in HIn.
                destruct HIn as [[key tree] [HIn [el_fst_eq update_eq]]]; simpl in *.
                destruct el_fst_eq.
                case_eq (ident_beq key v).
                all: move=> H; rewrite H in update_eq.
                {
                    rewrite ident_beq_eq in H; destruct H.
                    rewrite Forall_forall in imp_partial_valid'.
                    apply imp_partial_valid' in HIn.
                    clear imp_partial_valid' update_ctxt_soundness imp_partial_valid.
                    clear type_soundness is_map fst_eq HEq_map_fst AllVarValid fst_eq' type_soundness'.
                    clear distinct' find_exists fst_eq'' dependancies dependancies'0 ctxt' tctxt.
                    destruct tree as [[num|typ]|trees]; simpl in *.
                    1,3: by idtac.
                    inversion update_eq as [H']; destruct H'; clear update_eq; simpl.
                    split; trivial.
                    move=> pos l' HInf top_eq.
                    destruct HIn as [not_pdef not_def].
                    case_eq (pos =? length eqns_hd).
                    2: rewrite <-not_true_iff_false.
                    all: rewrite Nat.eqb_eq; move=> HEq; split; move=> H.
                    {
                        destruct H as [-> <-]; clear HEq.
                        unfold partial_defined_in.
                        rewrite nth_error_app2; auto.
                        rewrite Nat.sub_diag; simpl.
                        do 3 eexists; repeat split.
                        by exact (LRnil _).
                        exists (length vars_hd); split; trivial.
                        rewrite nth_error_app2; trivial.
                        rewrite Nat.sub_diag; simpl.
                        right; auto.
                    }
                    {
                        symmetry in HEq; destruct HEq.
                        split; [> reflexivity | idtac ].
                        move: (not_pdef _ top_eq); clear not_pdef not_def; move=> not_pdef.
                        unfold partial_defined_in in H, not_pdef.
                        rewrite <-app_assoc in not_pdef; simpl in not_pdef.
                        rewrite nth_error_app2 in H, not_pdef.
                        2: by apply/leP; assumption.
                        rewrite Nat.sub_diag in H, not_pdef; simpl in H, not_pdef.
                        destruct H as [vL [e [ind [HEq [is_spec [i [InfEq H]]]]]]].
                        destruct (leq_Cases _ _ InfEq) as [<-|SInf].
                        {
                            inversion HEq as [[H1 H2]]; destruct H1.
                            rewrite nth_error_app2 in H; trivial.
                            rewrite Nat.sub_diag in H; simpl in H.
                            destruct H as [Abs|[_ Eq]]; [> inversion Abs | rewrite Eq in is_spec ].
                            inversion is_spec; reflexivity.
                        }
                        {
                            exfalso; apply not_pdef.
                            do 3 eexists; split; [> exact HEq | idtac ].
                            split; [> exact is_spec | exists i ].
                            rewrite app_length; simpl; rewrite Nat.add_1_r.
                            split; assumption.
                        }
                    }
                    {
                        destruct H as [Abs _].
                        exfalso; exact (HEq Abs).
                    }
                    {
                        destruct (leq_Cases _ _ HInf) as [Abs|HInf'].
                        {
                            symmetry in Abs.
                            exfalso; exact (HEq Abs).
                        }
                        rewrite <-app_assoc in not_def; simpl in not_def.
                        by apply not_def in H.
                    }
                }
                {
                    destruct update_eq.
                    rewrite Forall_forall in imp_partial_valid'.
                    apply imp_partial_valid' in HIn.
                    rewrite <- app_assoc in HIn; simpl in HIn.
                    move: H HIn; clear.
                    rewrite <- not_true_iff_false; rewrite ident_beq_eq.
                    move=> HNeq.
                    rewrite app_length; simpl; rewrite Nat.add_1_r.
                    apply partial_valid_dtree_change_name; auto.
                }
            }
        }
        {
            move: (HRec dependancies); clear HRec; move=> HRec.
            destruct update_vars as [dependancies'0|].
            2: by idtac.
            move=> HEq is_map fst_eq type_soundness imp_partial_valid.
            specialize HRec with dependancies'0; move: HRec; impl_tac; trivial.
            impl_tac; trivial.
            impl_tac; trivial.
            impl_tac; trivial.
            impl_tac.
            {
                rewrite app_length; simpl; rewrite Nat.add_1_r.
                rewrite addn1; rewrite addSn.
                rewrite addn1 in imp_partial_valid.
                rewrite addnS in imp_partial_valid.
                rewrite <-app_assoc; simpl; trivial.
            }
            move=> [Allvalid [Allsubs [HEq_map_fst [type_soundness' imp_partial_valid']]]].
            move: (update_ctxt_soundness (update_def_tree ind (length eqns_hd)) dependancies'0 v).
            impl_tac.
            {
                rewrite <-HEq_map_fst; trivial.
            }
            destruct update_ctxt as [ctxt'|].
            2: by idtac.
            move=> H; move: (H ctxt'); clear H.
            impl_tac; trivial.
            inversion HEq as [H']; destruct H'; clear HEq.
            move=> [find_nNone [is_map' [fst_eq' update_ctxt_soundness]]].
            repeat split.
            {
                constructor; simpl; auto.
                {
                    move: update_ctxt_soundness find_nNone type_soundness'; clear.
                    move=> H; move: tctxt.
                    induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl; trivial.
                    by move=> tctxt H _; apply H; reflexivity.
                    move=> [|[k3 v3] t3]; simpl in *.
                    by move=> _ H; inversion H.
                    destruct H_hd as [[] H_hd].
                    rewrite ident_beq_sym in H_hd; destruct ident_beq.
                    {
                        move=> _ H; inversion H.
                        exact (update_def_tree_valid _ _ _ _ H_hd).
                    }
                    {
                        move=> find_nNone H; inversion H.
                        apply (HRec t3); auto.
                    }
                }
                {
                    move: fst_eq' Allvalid update_ctxt_soundness; clear.
                    do 2 rewrite List.Forall_forall.
                    move=> fst_eq valid_in rel var LIn; apply valid_in in LIn; clear valid_in.
                    destruct var as [v'|[v'|] ind']; simpl in *.
                    3: by idtac.
                    {
                        move=> find; apply LIn; move: fst_eq find; clear.
                        move: ctxt'.
                        induction dependancies'0 as [|[key val] tl HRec]; simpl; trivial.
                        move=> [|[key' val'] tl']; simpl; [> by idtac | idtac ].
                        move=> H; inversion H.
                        by destruct ident_beq; [> discriminate | apply HRec ].
                    }
                    {
                        move: rel LIn; clear.
                        move=> LR; induction LR as [|[k1 v1] [k2 v2] t1 t2 rel_hd rel_tl].
                        all: simpl; auto.
                        simpl in *; destruct rel_hd as [[] H].
                        destruct (ident_beq v'); trivial.
                        destruct ident_beq; [> idtac | by destruct H].
                        move: (update_def_tree_subtree _ _ _ _ H).
                        move=> is_sub valid.
                        exact (sub_dtree_keep_access _ _ _ valid is_sub).
                    }
                }
            }
            {
                refine (list_rel_trans sub_dtree_trans _ _ _ Allsubs _).
                move: update_ctxt_soundness; clear.
                move=> H; induction H as [|[k1 v1] [k2 v2] t1 t2 rel_hd rel_tl HRec]; simpl in *.
                all: constructor; trivial.
                destruct rel_hd as [[] HEq].
                destruct ident_beq.
                by refine (update_def_tree_subtree _ _ _ _ HEq).
                by destruct HEq; refine (sub_dtree_refl _).
            }
            {
                rewrite HEq_map_fst; auto.
            }
            {
                move: update_ctxt_soundness type_soundness'; clear.
                move=> H; move: tctxt.
                induction H as [|[k1 v1] [k2 v2] t1 t2 rel_hd rel_tl HRec]; simpl in *; trivial.
                move=> [|[k3 v3] t3] H; simpl in *; inversion H.
                constructor; simpl; auto.
                destruct rel_hd as [[] HEq].
                destruct ident_beq.
                by refine (update_def_tree_type_soundness _ _ _ _ _ HEq _); assumption.
                by destruct HEq; assumption.
            }
            {
                rewrite Forall_forall.
                move=> [v' t'] HIn.
                destruct (list_rel_imp_In_r _ _ update_ctxt_soundness _ HIn)
                        as [[v'' t''] [LIn [HEq update_eq]]].
                simpl in *.
                destruct HEq; clear HIn.
                case_eq (ident_beq v'' v).
                all: move=> H; rewrite H in update_eq.
                {
                    rewrite ident_beq_eq in H; destruct H.
                    rewrite Forall_forall in imp_partial_valid'.
                    apply imp_partial_valid' in LIn.
                    move :(update_def_tree_soundness _ _ _ _ update_eq eqns_tl vars_hd tl expr v'' nil nil).
                    simpl.
                    move=> H; apply H; clear H.
                    2: by constructor.
                    rewrite app_length in LIn; simpl in LIn; rewrite Nat.add_1_r in LIn.
                    rewrite addn1.
                    rewrite <-app_assoc in LIn; simpl in LIn; assumption.
                }
                {
                    destruct update_eq.
                    rewrite Forall_forall in imp_partial_valid'.
                    apply imp_partial_valid' in LIn; auto.
                    rewrite app_length in LIn; simpl in LIn.
                    rewrite Nat.add_1_r in LIn.
                    rewrite <- app_assoc in LIn; simpl in LIn.
                    move: LIn; apply partial_valid_dtree_change_name.
                    rewrite <-not_true_iff_false in H; rewrite ident_beq_eq in H.
                    auto.
                }
            }
        }
    }
Qed.

Theorem remove_await_tree_soundness:
    forall v eqns t t',
        remove_await_tree t = Some t' ->
            same_dtree t t' /\
            (forall path,
                partial_valid_def_tree 0 v t path eqns ->
                valid_def_tree v t' path eqns) /\
            (forall typ,
                def_tree_of_type  t typ ->
                def_tree_of_type' t' typ).
Proof.
    move=> v eqns.
    refine (def_tree_find _ _
        (fun trees => forall pos trees',
            remove_await_trees trees = Some trees' ->
                same_dtrees trees trees' /\
                (forall path,
                    partial_valid_list_def_tree 0 v trees pos path eqns ->
                    valid_list_def_tree v trees' pos path eqns) /\
                (forall typ,
                    list_def_tree_of_type trees typ (dtrees_length trees) ->
                    list_def_tree_of_type' trees' typ (dtrees_length trees)))
        _ _ _ _); simpl.
    {
        move=> [i|typ] t' H; inversion H as [H'].
        clear H H' t'; simpl.
        split; [> by constructor | idtac ].
        split; trivial.
        move=> path [_ H] l' pos top_eq.
        move: (H pos l'); impl_tac; auto.
    }
    {
        move=> trees HRec trees'.
        destruct remove_await_trees as [trees''|].
        2: by idtac.
        move=> H; inversion H as [H']; clear H H' trees'; simpl.
        destruct (HRec 0 _ Logic.eq_refl) as [same [HRec_valid HRec_ts]].
        split; [> by constructor; assumption | idtac ].
        split.
        {
            move=> path [H H']; split.
            by move=> pos; apply H; auto.
            auto.
        }
        {
            move=> [|d m|typ len]; auto.
            move=> type_soundness.
            rewrite <-(list_def_tree_of_type_length _ _ _ type_soundness).
            apply HRec_ts.
            rewrite (list_def_tree_of_type_length _ _ _ type_soundness); assumption.
        }
    }
    {
        move=> pos trees' H; inversion H; simpl.
        split; [> constructor | auto ].
    }
    {
        move=> hd HRec_hd tl HRec_tl pos trees'.
        destruct remove_await_tree as [hd'|].
        2: by idtac.
        destruct remove_await_trees as [tl'|].
        2: by idtac.
        move=> H; inversion H as [H']; clear H H' trees'.
        simpl.
        destruct (HRec_hd _ Logic.eq_refl) as [same_hd [valid_hd hd_ts]].
        destruct (HRec_tl pos.+1 _ Logic.eq_refl) as [same_tl [valid_tl tl_ts]].
        split; [> constructor; assumption | idtac ].
        split; intro; move=> []; intros; split; auto.
    }
Qed.

Theorem clean_def_tree_soundness:
    forall eqns dependancies types dependancies',
        clean_def_tree dependancies = Some dependancies' ->
        list_rel def_tree_of_type (map snd dependancies) types ->
        (forall v t, List.In (v, t) dependancies -> partial_valid_def_tree 0 v t nil eqns) ->
        map fst dependancies = map fst dependancies' /\
        list_rel (fun t1 t2 => match t2 with | Some t2 => same_dtree t1 t2 | None => True end)
            (map snd dependancies) (map snd dependancies') /\
        (forall v, List.In (v, None) dependancies' ->
            forall pos path_in, defined_in v path_in pos eqns -> False) /\
        (forall v t, List.In (v, Some t) dependancies' -> valid_def_tree v t nil eqns) /\
        list_rel (fun d typ => match d with
            | Some d => def_tree_of_type' d typ
            | None => True end) (map snd dependancies') types.
Proof.
    move=> eqns dependancies; induction dependancies as [|[v t] tl HRec]; simpl.
    {
        move=> types d' H; inversion H; clear; simpl.
        move=> H; inversion H; intros H'.
        split; [> reflexivity | idtac ].
        split; [> by constructor | idtac ].
        split; [> by idtac | idtac ].
        by split; [> idtac | constructor ].
    }
    {
        destruct t as [[eq_num|typ]|trees].
        all: swap 1 2.
        {
            destruct clean_def_tree as [tl'|].
            all: move=> types dependancies' H type_soundness Hvalid; inversion H.
            destruct types as [|typ' types].
            all: inversion type_soundness.
            specialize HRec with types tl'; move: HRec.
            impl_tac; trivial.
            impl_tac; trivial.
            impl_tac.
            by intros; apply Hvalid; auto.
            move=> [HEq [same_trees [undef [Hvalid' type_soundness']]]]; simpl.
            split; [> idtac | split; [> idtac | split ] ].
            by f_equal; assumption.
            by constructor; trivial.
            {
                move=> v' [HEq'|LIn].
                2: apply undef; assumption.
                inversion HEq' as [H']; destruct H'.
                specialize Hvalid with v (DTBase _ (IoAA typ)).
                move=> pos path_in.
                move: Hvalid; impl_tac.
                by left; reflexivity.
                simpl.
                move=> H'; apply H'; trivial.
                constructor.
            }
            split.
            {
                move=> v' t [Abs|LIn]; apply Hvalid'; trivial.
                inversion Abs.
            }
            {
                constructor; trivial.
            }
        }
        all: [> pose (t := DTBase _ (IoAI eq_num)) | pose (t := DTRec _ trees)].
        all: fold t; move: t; [> clear eq_num | clear trees ]; move=> t.
        all: move=> types dependancies' H type_soundness.
        all: move: dependancies' H.
        all: destruct types as [|typ types]; inversion type_soundness.
        all: move: (remove_await_tree_soundness v eqns t).
        all: destruct remove_await_tree as [t'|].
        2,4: by idtac.
        all: destruct clean_def_tree as [tl'|].
        2,4: by idtac.
        all: move=> Hvalid_t' d' HEq Hvalid_in.
        all: destruct (Hvalid_t' _ Logic.eq_refl) as [same_tree [valid t'_ts]].
        all: inversion HEq as [H']; clear HEq H' d'.
        all: move: (HRec types tl'); clear HRec.
        all: impl_tac; trivial.
        all: impl_tac; trivial.
        all: impl_tac.
        1,3: by intros; apply Hvalid_in; auto.
        all: move=> [HEq [same_trees [undef [valid_out type_soundness_out]]]].
        all: simpl; split.
        1,3: by f_equal.
        all: split.
        1,3: by constructor; trivial.
        all: split.
        1,3: move=> v' [Abs|LIn]; [ by inversion Abs | by apply undef].
        all: split.
        2,4: constructor; auto.
        all: move=> v0 t0 [PairEq|LIn].
        2,4: apply valid_out; auto.
        all: inversion PairEq as [[Eq1 Eq2]].
        all: destruct Eq1; destruct Eq2; clear PairEq.
        all: apply valid; trivial.
        all: apply Hvalid_in; auto.
    }
Qed.

Lemma valid_is_defined_in:
    forall v eqns i path_in path_tl dtree,
        valid_def_tree v dtree path_in eqns ->
        dtree_defined dtree path_tl i <->
            valid_dtree_access' dtree path_tl /\
            defined_in v (path_in ++ path_tl) i eqns.
Proof.
    move=> v eqns i path_in path_tl; move: path_in.
    induction path_tl as [|path_hd path_tl HRec]; move=> path_in [eq_num|dtrees]; simpl.
    {
        move=> H; rewrite cats0.
        specialize H with path_in i; rewrite <-H.
        {
            split.
            by move=> [H1 H2]; auto.
            by move=> [_ [H1 H2]]; auto.
        }
        clear; induction path_in; constructor; trivial.
    }
    {
        move=> [ndef _]; split.
        by move=> [].
        by move=> [_]; rewrite cats0; exact (ndef _).
    }
    {
        move=> <-.
        2: by clear; induction path_in; simpl; constructor; trivial.
        split.
        by move=> [Abs _]; discriminate Abs.
        move=> [H _]; discriminate H.
    }
    {
        assert (forall path_hd pos,
            valid_list_def_tree v dtrees pos path_in eqns ->
            dtrees_defined dtrees path_tl path_hd i <->
            path_hd < dtrees_length dtrees /\
            valid_dtrees_access' dtrees path_hd path_tl /\
            defined_in v (path_in ++ (pos + path_hd) :: path_tl) i eqns) as H.
        {
            clear path_hd.
            induction dtrees as [|dtree dtrees HRec']; simpl.
            {
                move=> path_hd pos _; split.
                by move=> [].
                move=> [Abs _].
                move/ltP in Abs; exact (Nat.nlt_0_r _ Abs).
            }
            move=> [|path_hd].
            {
                move=> pos; rewrite addn0; rewrite add1n.
                move=> [valid_hd _]; rewrite HRec.
                2: by exact valid_hd.
                rewrite <-app_assoc; simpl.
                split.
                by move=> [H1 H2]; auto.
                move=> [_ [H H1]].
                split; assumption.
            }
            {
                move=> pos [_ valid_tl].
                rewrite HRec'; [> rewrite add1n | exact valid_tl].
                rewrite addnS; rewrite addSn.
                split; move=> [H [H1 H2]]; auto.
            }
        }
        specialize H with path_hd 0.
        move=> [_ H1]; rewrite H; trivial.
        rewrite add0n; split.
        {
            clear.
            move=> [H [H1 H2]].
            split; [> idtac | assumption ].
            split; assumption.
        }
        {
            clear.
            move=> [[H H1] H2].
            split; [> idtac | split ]; assumption.
        }
    }
Qed.

Lemma is_spec_preserve_dtree_valid_access {A}:
    forall path_nat path_in (dtree : def_tree A),
        list_rel is_specialization path_nat path_in ->
        valid_dtree_access dtree path_in ->
        valid_dtree_access' dtree path_nat.
Proof.
    move=> path_nat path_in dtree lr; move: dtree.
    induction lr as [|pnat_hd pin_hd pnat_tl pin_tl is_spec_hd is_spec_tl HRec].
    all: move=> [base|dtrees]; simpl.
    1-3: move=> H; exact H.
    inversion is_spec_hd as [ae i eval_eq|ae aeL i LIn eval_eq|ae1 ae2 i1 i2 i eval_eq1 eval_eq2 Ineq].
    {
        rewrite eval_eq.
        move=> [_ [tmp valid_acc]].
        inversion tmp as [|hd tl inf_length].
        split; [> assumption | idtac ].
        assert (forall pos pnat_hd,
            valid_dtrees_access dtrees pos [:: pnat_hd + pos] pin_tl ->
            pnat_hd < dtrees_length dtrees ->
            valid_dtrees_access' dtrees pnat_hd pnat_tl
        ) as imp_valid.
        2: by apply (imp_valid 0); [> rewrite addn0 | idtac ]; assumption.
        move: HRec; clear; move=> HRec.
        induction dtrees as [|dtree dtrees HRec_trees]; simpl.
        by auto.
        move=> pos [|pnat_hd].
        {
            rewrite add0n; rewrite Nat.eqb_refl; simpl.
            move=> [_ H] _; apply HRec; assumption.
        }
        {
            move=> [H _] SInf; apply (HRec_trees pos.+1).
            by rewrite addnS; rewrite addSn in H; assumption.
            by rewrite add1n in SInf; auto.
        }
    }
    {
        case_eq (fold_right (fun ae l => l' <- l; i <- eval_arith_expr nil ae; Some (i :: l')) (Some nil) aeL).
        2: by move=> _ [].
        move=> iL fold_eq [_ [Forall_inf valid]].
        assert (List.In (0 + pnat_hd) iL) as LIn_iL.
        {
            rewrite add0n.
            move: LIn fold_eq eval_eq; clear; move: iL.
            induction aeL as [|ae_hd ae_tl HRec]; simpl.
            by move=> iL [].
            move=> iL [<-|LIn]; destruct fold_right.
            2,4: move=> H; discriminate H.
            all: destruct (eval_arith_expr nil ae_hd).
            all: move=> H; inversion H as [H']; destruct H'; clear H.
            by move=> H; inversion H; simpl; left; reflexivity.
            move=> eval_eq; simpl; right.
            exact (HRec _ LIn Logic.eq_refl eval_eq).
        }
        rewrite Forall_forall in Forall_inf.
        move: (Forall_inf _ LIn_iL); move=> inf_len.
        rewrite add0n in inf_len.
        split; [> assumption | idtac ].
        move: HRec inf_len LIn_iL valid; clear; move=> HRec.
        pose (pos := 0); fold pos; move: pos pnat_hd.
        induction dtrees as [|hd tl HRec_trees]; simpl; [> by auto | idtac ].
        move=> pos [|pnat_hd].
        {
            rewrite addn0; move=> _ LIn.
            assert (List.existsb (Nat.eqb pos) iL = true) as ->.
            {
                rewrite List.existsb_exists; exists pos.
                split; [> assumption | exact (Nat.eqb_refl _)].
            }
            move=> [_ valid]; exact (HRec _ valid).
        }
        {
            rewrite add1n; rewrite addnS; rewrite <-addSn.
            move=> SInf LIn [valid _].
            apply (HRec_trees pos.+1 pnat_hd); auto.
        }
    }
    {
        rewrite eval_eq1; rewrite eval_eq2.
        rewrite <-gen_range_completeness in Ineq.
        move=> [_ [all_inf valid]].
        rewrite Forall_forall in all_inf.
        move: (all_inf _ Ineq); move=> inf_len.
        split; [> assumption | idtac ].
        assert (List.In (pnat_hd + 0) (gen_range i1 i2)) as LIn'
            by (rewrite addn0; assumption).
        move: HRec inf_len LIn' valid; clear; move=> HRec.
        pose (pos := 0); fold pos; move: pos pnat_hd.
        induction dtrees as [|hd tl HRec_trees]; simpl; [> by auto | idtac ].
        move=> pos [|pnat_hd].
        {
            rewrite add0n; move=> _ LIn.
            assert (List.existsb (Nat.eqb pos) (gen_range i1 i2) = true) as ->.
            {
                rewrite List.existsb_exists; exists pos.
                split; [> assumption | exact (Nat.eqb_refl _)].
            }
            move=> [_ valid]; exact (HRec _ valid).
        }
        {
            rewrite add1n; rewrite addSn; rewrite <-addnS.
            move=> SInf LIn [valid _].
            apply (HRec_trees pos.+1 pnat_hd); auto.
        }
    }
Qed.
