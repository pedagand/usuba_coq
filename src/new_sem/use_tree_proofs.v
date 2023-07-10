Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST usuba_ASTProp arch
    list_relations termination_funs termination_properties
    semantic_base semantic_base_proofs coq_missing_lemmas.

Lemma list_use_tree_of_type_length:
    forall typ trees len,
        list_use_tree_of_type trees typ len -> utrees_length trees = len.
Proof.
    move=> typ; induction trees as [|hd tl HRec]; simpl; auto.
    move=> [|len] [_ H]; [> by destruct H | f_equal; auto ].
Qed.

(* Properties about subtrees *)

Lemma sub_utree_refl:
    forall t, sub_utree t t.
Proof.
    refine (use_tree_find _ (fun t => sub_utrees t t) _ _ _ _).
    all: by intros; constructor.
Qed.

Lemma sub_utree_trans:
    forall x y z, sub_utree x y -> sub_utree y z -> sub_utree x z.
Proof.
    move=> x y z H; move: x y H z.
    refine (sub_utree_find _ (fun l1 l2 H1 => forall l3, sub_utrees l2 l3 -> sub_utrees l1 l3) _ _ _ _).
    by intros; constructor.
    {
        move=> l1 l2 u1 u2 H12 HRec t3 H23; inversion H23.
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

Lemma sub_utrees_length :
    forall l1 l2,
        sub_utrees l1 l2 -> utrees_length l1 = utrees_length l2.
Proof.
    move=> l1; induction l1 as [|h1 t2 HRec]; simpl.
    all: move=> l2 H; inversion H; simpl; auto.
Qed.

Lemma sub_utree_keep_access :
    forall path t1 t2,
        valid_utree_access t1 path ->
        sub_utree t1 t2 ->
        valid_utree_access t2 path.
Proof.
    move=> path; induction path as [|ind tl HRec].
    by move=> [u1 b1|u1 t1] [u2 b2|u2 t2]; simpl; trivial.
    move=> [u1 b1|u1 t1] t2' valid1 H; simpl in valid1.
    by discriminate.
    inversion H as [|l1 l2 u1' u2' sub_l H1 H2]; destruct H1; destruct H2; clear H.
    simpl; destruct ind as [ae|ae1 ae2|aeL].
    {
        destruct eval_arith_expr as [i|]; [> idtac | by idtac ].
        destruct valid1 as [not_empty [all_inf valid]].
        split; [> assumption | idtac ].
        rewrite <-(sub_utrees_length _ _ sub_l); split; trivial.
        move: sub_l HRec valid; clear; move=> sub_l Himp.
        pose (p := 0); fold p; move: p.
        induction sub_l as [|h1 h2 t1 t2 sub_hd sub_tl HRec]; simpl; trivial.
        move=> pos [valid1 H]; split; auto.
        destruct (_ =? _); simpl in *; trivial.
        apply (Himp h1); trivial.
    }
    {
        destruct eval_arith_expr; [> idtac | by idtac ].
        destruct eval_arith_expr; [> idtac | by idtac ].
        destruct valid1 as [not_empty [all_inf valid]].
        split; [> assumption | idtac ].
        rewrite <-(sub_utrees_length _ _ sub_l); split; trivial.
        move: sub_l HRec valid; clear; move=> sub_l Himp.
        pose (p := 0); fold p; move: p.
        induction sub_l as [|h1 h2 t1 t2 sub_hd sub_tl HRec]; simpl; trivial.
        move=> pos [valid1 H]; split; auto.
        destruct List.existsb; simpl in *; trivial.
        apply (Himp h1); trivial.
    }
    {
        destruct fold_right; [> idtac | by idtac ].
        destruct valid1 as [not_empty [all_inf valid]].
        split; [> assumption | idtac ].
        rewrite <-(sub_utrees_length _ _ sub_l); split; trivial.
        move: sub_l HRec valid; clear; move=> sub_l Himp.
        pose (p := 0); fold p; move: p.
        induction sub_l as [|h1 h2 t1 t2 sub_hd sub_tl HRec]; simpl; trivial.
        move=> pos [valid1 H]; split; auto.
        destruct List.existsb; simpl in *; trivial.
        apply (Himp h1); trivial.
    }
Qed.

(* Functions soundness *)

Lemma utrees_length_build:
    forall len pos indices t1 t2,
    utrees_length (build_use_trees pos len indices t1 t2) = len.
Proof.
    move=> len; induction len as [|len HRec]; simpl; trivial.
    move=> pos indices t1 t2; destruct List.existsb; simpl; rewrite HRec; reflexivity.
Qed.

Lemma build_use_tree_from_type_access:
    forall path_tl len_eqns_hd uses typ tree',
        build_use_tree_from_type path_tl uses typ len_eqns_hd = Some tree' ->
            valid_utree_access tree' path_tl.
Proof.
    move=> path_tl len_eqns_hd.
    induction path_tl as [|ind path_tl HRec]; simpl.
    {
        move=> uses typ tree' H.
        inversion H as [H']; clear H H' tree'.
        simpl; constructor.
    }
    {
        move=> uses [|d m|typ len].
        1,2: by idtac.
        move: (HRec nil typ); clear HRec; move=> HRec.
        destruct build_use_tree_from_type as [next_tree|].
        2: by idtac.
        move: (HRec _ Logic.eq_refl); clear HRec; move=> type_of tree'.
        destruct ind as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i HEq; simpl | by idtac].
            case_eq (i <? len); simpl; move=> Hlt H.
            all: inversion H as [H']; clear H H' tree'.
            simpl; rewrite HEq.
            split.
            by move=> H; inversion H.
            split.
            {
                rewrite utrees_length_build.
                constructor; [> idtac | constructor ].
                apply/ltP; rewrite <-Nat.ltb_lt; assumption.
            }
            {
                move: type_of; clear; move=> valid_utree.
                pose (pos := 0); fold pos; move: pos.
                induction len; simpl; [> constructor | idtac ].
                move=> pos; case_eq (pos =? i); simpl; move=> ->; simpl; split; auto.
            }
        }
        {
            case_eq (eval_arith_expr nil ae1); [> move=> i1 HEq1; simpl | discriminate ].
            case_eq (eval_arith_expr nil ae2); [> move=> i2 HEq2; simpl | discriminate ].
            case_eq (forallb (Nat.ltb^~ len) (gen_range i1 i2)); [> move=> HInf; simpl | discriminate ].
            assert (List.existsb xpredT (gen_range i1 i2) = true) as ->.
            {
                rewrite List.existsb_exists; eexists.
                split; [> exact (gen_range_in_r _ _) | reflexivity].
            }
            move=> H.
            inversion H as [H']; clear H H' tree'; simpl.
            rewrite List.forallb_forall in HInf.
            rewrite HEq1; rewrite HEq2; split; [> idtac | split ].
            {
                clear; move=> Abs.
                move: (gen_range_in_l i1 i2); rewrite Abs; simpl.
                trivial.
            }
            {
                rewrite Forall_forall.
                move=> x LIn; apply HInf in LIn.
                rewrite Nat.ltb_lt in LIn.
                rewrite utrees_length_build; apply/ltP; assumption.
            }
            {
                move: type_of; clear.
                pose (p := 0); fold p; move=> H; move: p.
                induction len; simpl; trivial.
                move=> p; case_eq (List.existsb (Nat.eqb p) (gen_range i1 i2)); simpl; move=> ->; split; auto.
            }
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            case_eq (forallb (Nat.ltb^~ len) iL && List.existsb xpredT iL); move=> Hlt H.
            all: inversion H as [H']; clear H H' tree'.
            move/andP in Hlt; unfold is_true in Hlt.
            destruct Hlt as [Hlt not_empty].
            simpl; rewrite HEq.
            split; [> idtac | split ].
            {
                move=> H; rewrite H in not_empty; simpl in *.
                inversion not_empty.
            }
            {
                rewrite List.forallb_forall in Hlt; rewrite Forall_forall.
                move=> x HIn; apply Hlt in HIn.
                rewrite utrees_length_build; rewrite Nat.ltb_lt in HIn.
                apply/ltP; assumption.
            }
            {
                move: type_of; clear.
                pose (p := 0); fold p; move=> H; move: p.
                induction len; simpl; trivial.
                move=> p; case_eq (List.existsb (Nat.eqb p) iL); simpl; move=> ->; split; auto.
            }
        }
    }
Qed.

Lemma build_use_tree_from_type_type_soundness:
    forall path_tl len_eqns_hd uses typ tree',
    build_use_tree_from_type path_tl uses typ len_eqns_hd = Some tree' ->
            use_tree_of_type tree' typ.
Proof.
    move=> path_tl len_eqns_hd.
    induction path_tl as [|ind path_tl HRec]; simpl.
    {
        move=> uses typ tree' H.
        inversion H as [H']; clear H H' tree'.
        simpl; reflexivity.
    }
    {
        move=> uses [|d m|typ len] tree'.
        1,2: by move=> H; inversion H.
        move: (HRec nil typ); clear HRec; move=> HRec.
        destruct build_use_tree_from_type as [next_tree|].
        2: by move=> H; inversion H.
        move: (HRec next_tree); clear HRec.
        impl_tac; [> reflexivity | move=> type_of].
        destruct ind as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i HEq; simpl | by idtac].
            case_eq (i <? len); simpl.
            all: move=> Hlt H; inversion H as [H']; clear H H' tree'.
            simpl; move: type_of.
            assert (i < len + 0) as H.
            {
                rewrite addn0; apply/ltP; rewrite <-Nat.ltb_lt; assumption.
            }
            move: H.
            pose (pos := 0); fold pos; move: pos; clear.
            induction len as [|len HRec]; simpl; [> reflexivity | move=> pos HInf type_of].
            specialize HRec with pos.+1.
            rewrite addSn in HInf; rewrite addnS in HRec.
            destruct (_ || _); simpl; split; auto.
        }
        {
            case_eq (eval_arith_expr nil ae1); [> move=> i1 HEq1; simpl | by idtac].
            case_eq (eval_arith_expr nil ae2); [> move=> i2 HEq2; simpl | by idtac].
            case_eq (forallb (Nat.ltb^~ len) (gen_range i1 i2) && List.existsb xpredT (gen_range i1 i2)); simpl.
            all: move=> Hlt H; inversion H as [H']; clear H H' tree'.
            simpl; move: type_of.
            assert (Forall (fun i => i < len + 0) (gen_range i1 i2)) as H.
            {
                move/andP in Hlt; destruct Hlt as [Hlt _]; unfold is_true in Hlt.
                rewrite List.forallb_forall in Hlt; rewrite Forall_forall.
                move=> x LIn; apply Hlt in LIn.
                rewrite addn0; apply/ltP; rewrite <-Nat.ltb_lt; assumption.
            }
            move: H.
            pose (pos := 0); fold pos; move: pos; clear.
            induction len as [|len HRec]; simpl; [> reflexivity | move=> pos HInf type_of].
            specialize HRec with pos.+1.
            rewrite addSn in HInf; rewrite addnS in HRec.
            destruct List.existsb; simpl; split; auto.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            case_eq (forallb (Nat.ltb^~ len) iL && List.existsb xpredT iL); simpl.
            all: move=> Hlt H; inversion H as [H']; clear H H' tree'.
            simpl; move: type_of.
            assert (Forall (fun i => i < len + 0) iL) as H.
            {
                move/andP in Hlt; destruct Hlt as [Hlt _]; unfold is_true in Hlt.
                rewrite List.forallb_forall in Hlt; rewrite Forall_forall.
                move=> x LIn; apply Hlt in LIn.
                rewrite addn0; apply/ltP; rewrite <-Nat.ltb_lt; assumption.
            }
            move: H.
            pose (pos := 0); fold pos; move: pos; clear.
            induction len as [|len HRec]; simpl; [> reflexivity | move=> pos HInf type_of].
            specialize HRec with pos.+1.
            rewrite addSn in HInf; rewrite addnS in HRec.
            destruct List.existsb; simpl; split; auto.
        }
    }
Qed.

Lemma build_use_tree_from_type_soundness:
    forall path_tl vars eqns_hd eqns_tl expr eL uses typ v tree',
        build_use_tree_from_type path_tl uses typ (length eqns_hd) = Some tree' ->
            forall path_in path_nat,
                list_rel is_specialization path_nat path_in ->
                is_subexpr (ExpVar (Index (Var v) (path_in ++ path_tl))) expr ->
                (forall pos l', List.In pos uses /\ l' = nil <->
                    ((length eqns_hd) <= pos /\
                        if length eqns_hd =? pos
                        then partial_used_in v (path_nat ++ l') eL
                        else used_in v (path_nat ++ l') pos (eqns_hd ++ (vars, expr) :: eqns_tl))) ->
                partial_valid_use_tree' (length eqns_hd) (ExpVar (Index (Var v) (path_in ++ path_tl)) :: eL) v tree' path_nat
                (eqns_hd ++ (vars, expr) :: eqns_tl).
Proof.
    move=> path_tl vars eqns_hd eqns_tl e eL.
    induction path_tl as [|ind path_tl HRec]; simpl.
    {
        move=> uses typ v tree' H.
        inversion H as [H']; clear H H' tree'; simpl.
        move=> path_in path_nat is_spec HIn valid pos l'.
        specialize valid with pos l'; split.
        {
            move=> [[HEq|ListIn] l'_is_nil].
            all: symmetry in l'_is_nil; destruct l'_is_nil.
            {
                destruct HEq.
                split; trivial.
                rewrite Nat.eqb_refl; clear valid.
                rewrite cats0; unfold partial_used_in.
                eexists; split.
                by exact is_spec.
                eexists; split.
                by constructor 1.
                rewrite cats0.
                simpl; left; constructor.
            }
            {
                destruct valid as [H _]; move: H; impl_tac; auto.
                move=> [HInf valid]; split; trivial.
                case_eq (length eqns_hd =? pos).
                all: move=> H; rewrite H in valid; auto.
                rewrite cats0; unfold partial_used_in.
                eexists; split.
                by exact is_spec.
                eexists; split.
                by constructor 1.
                rewrite cats0.
                simpl; left; constructor.
            }
        }
        {
            move=> [HInf used_prop].
            destruct (leq_Cases _ _ HInf) as [|HSInf].
            {
                destruct H; rewrite Nat.eqb_refl in used_prop.
                unfold partial_used_in in used_prop.
                destruct used_prop as [ind [is_spec' [e' [ListIn HEq]]]].
                inversion ListIn as [H|].
                {
                    destruct H; clear ListIn.
                    split; auto.
                    destruct HEq as [H|[Abs _]].
                    2: by inversion Abs.
                    inversion H as [H']; destruct H'; clear H.
                    destruct (list_rel_append is_specialization path_nat path_in l' nil) as [H _].
                    move: H; impl_tac.
                    {
                        split; trivial.
                        apply list_rel_length in is_spec; auto.
                    }
                    move=> [_ H].
                    apply list_rel_length in H; destruct l'; simpl in H; auto.
                    discriminate H.
                }
                {
                    destruct valid as [_ H']; move: H'; impl_tac.
                    {
                        split; trivial.
                        rewrite Nat.eqb_refl.
                        unfold partial_used_in.
                        eexists; split.
                        by exact is_spec'.
                        exists e'; split ;auto.
                    }
                    {
                        move=> []; auto.
                    }
                }
            }
            {
                assert (length eqns_hd =? pos = false) as HEq.
                {
                    rewrite <- not_true_iff_false; rewrite Nat.eqb_eq.
                    move=> H; destruct H.
                    apply (Nat.nle_succ_diag_l (length eqns_hd)).
                    apply/leP; assumption.
                }
                rewrite HEq in used_prop; rewrite HEq in valid.
                destruct valid as [_ []]; auto.
            }
        }
    }
    {
        move=> uses [|d m|typ len].
        1,2: by idtac.
        move: (HRec nil typ); clear HRec; move=> HRec.
        destruct build_use_tree_from_type as [next_tree|].
        2: by idtac.
        destruct ind as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i HEq; simpl | by idtac].
            move=> v tree' H.
            destruct (_ <? _); simpl in H.
            all: inversion H as [H']; clear H H' tree'.
            move: (HRec v next_tree).
            clear HRec.
            impl_tac; trivial.
            move=> HRec path_in path_nat is_spec HIn used_prop.
            move: (HRec (path_in ++ [:: IInd ae]) (path_nat ++ [:: i])); clear HRec.
            impl_tac.
            {
                rewrite list_rel_last; split; trivial.
                constructor; assumption.
            }
            rewrite <- app_assoc; simpl.
            impl_tac; trivial.
            impl_tac.
            {
                move=> pos l'; split.
                by move=> [[] _].
                specialize used_prop with pos (i :: l').
                rewrite <- app_assoc; simpl.
                rewrite <- used_prop.
                move=> [_ H]; discriminate.
            }
            move=> H.
            split.
            {
                move=> pos; split.
                {
                    move=> ListIn; specialize used_prop with pos nil.
                    rewrite cats0 in used_prop.
                    destruct used_prop as [[HInf partial] _]; auto.
                    split; trivial.
                    destruct (_ =? _); trivial.
                    move: partial.
                    unfold partial_used_in.
                    move=> [ind [is_spec' [e' [HIn' HEq']]]].
                    eexists; split.
                    by exact is_spec'.
                    exists e'; split; auto.
                    by constructor.
                }
                move=> [HInf Abs].
                destruct (leq_Cases _ _ HInf) as [HEq'|HSInf].
                {
                    destruct HEq'; rewrite Nat.eqb_refl in Abs.
                    specialize used_prop with (length eqns_hd) nil.
                    destruct used_prop as [_ []]; trivial.
                    split; trivial.
                    rewrite Nat.eqb_refl.
                    move: Abs; rewrite cats0.
                    unfold partial_used_in.
                    move=> [ind [is_spec' [e' [HIn' HEq2]]]].
                    exists ind; split; trivial.
                    exists e'; split; trivial.
                    inversion HIn' as [H'|]; trivial.
                    destruct H'; move: is_spec'.
                    simpl in HEq2.
                    destruct HEq2 as [Abs|[Abs _]]; inversion Abs.
                    move=> is_spec'.
                    apply list_rel_length in is_spec.
                    apply list_rel_length in is_spec'.
                    rewrite is_spec in is_spec'.
                    exfalso.
                    move: is_spec'; clear.
                    rewrite app_length; simpl.
                    induction (length path_in) as [|l HRec]; simpl.
                    by discriminate.
                    move=> H; apply HRec; inversion H as [H'].
                    do 2 rewrite <-H'; reflexivity.
                }
                {
                    case_eq (length eqns_hd =? pos).
                    all: move=> HEq'; rewrite HEq' in Abs.
                    {
                        rewrite Nat.eqb_eq in HEq'; destruct HEq'.
                        exfalso; apply (Nat.nle_succ_diag_l (length eqns_hd)).
                        apply/leP; trivial.
                    }
                    {
                        specialize used_prop with pos nil.
                        rewrite HEq' in used_prop.
                        destruct used_prop as [_ []]; trivial.
                        rewrite cats0; auto.
                    }
                }
            }
            {
                pose (pos := 0); fold pos; move: pos.
                induction len as [|len HRec]; simpl; trivial.
                move=> pos; specialize HRec with pos.+1.
                rewrite orb_false_r.
                case_eq (pos =? i); simpl.
                {
                    rewrite Nat.eqb_eq; move=> Eq; destruct Eq; auto.
                }
                {
                    move=> NEq; split; auto.
                    move=> pos'; split.
                    by move=> [].
                    move=> [HInf Abs].
                    destruct (leq_Cases _ _ HInf) as [HEq'|HSInf].
                    {
                        destruct HEq'; rewrite Nat.eqb_refl in Abs.
                        specialize used_prop with (length eqns_hd) (pos :: l').
                        rewrite <- app_assoc in Abs; simpl in Abs.
                        rewrite Nat.eqb_refl in used_prop.
                        destruct used_prop as [_ []]; [> idtac | by discriminate ].
                        split; trivial.
                        move: Abs; unfold partial_used_in.
                        move=> [ind [is_spec' [e' [HIn' HEq2]]]].
                        exists ind; split; trivial.
                        exists e'; split; trivial.
                        inversion HIn' as [H'|]; trivial.
                        destruct H'; move: is_spec'.
                        simpl in HEq2.
                        destruct HEq2 as [Abs|[Abs _]]; inversion Abs.
                        move=> is_spec'.
                        apply list_rel_length in is_spec.
                        destruct (list_rel_append is_specialization path_nat path_in (pos :: l') (IInd ae :: path_tl)) as [H' _].
                        move: H'; impl_tac; auto.
                        move=> [_ H']; inversion H' as [|h1 h2 t1 t2 AbsRel].
                        inversion AbsRel as [ae' i' Eq'| |].
                        rewrite HEq in Eq'.
                        rewrite <-not_true_iff_false in NEq; exfalso; apply NEq.
                        rewrite Nat.eqb_eq; inversion Eq'; auto.
                    }
                    {
                        case_eq (length eqns_hd =? pos').
                        all: move=> HEq'; rewrite HEq' in Abs.
                        {
                            rewrite Nat.eqb_eq in HEq'; destruct HEq'.
                            exfalso; apply (Nat.nle_succ_diag_l (length eqns_hd)).
                            apply/leP; trivial.
                        }
                        {
                            specialize used_prop with pos' (pos :: l').
                            rewrite <- app_assoc in Abs; simpl in Abs.
                            rewrite HEq' in used_prop.
                            destruct used_prop as [_ []]; auto.
                            discriminate.
                        }
                    }
                }
            }
        }
        {
            case_eq (eval_arith_expr nil ae1); [> move=> i1 HEq1 | discriminate].
            case_eq (eval_arith_expr nil ae2); [> move=> i2 HEq2 | discriminate].
            move=> v tree' H.
            destruct (_ && _); inversion H as [H']; clear H H' tree'.
            move: (HRec v next_tree); clear HRec.
            impl_tac; trivial; simpl.
            move=> H path_in path_nat is_spec HIn used_prop.
            move: (H (path_in ++ [:: IRange ae1 ae2])); clear H.
            rewrite <- app_assoc; simpl.
            move=> H.
            split.
            {
                move=> pos; split.
                {
                    specialize used_prop with pos nil.
                    rewrite cats0 in used_prop.
                    split; destruct used_prop as [[H1 partial] _]; auto.
                    destruct (_ =? _); auto.
                    move: partial.
                    unfold partial_used_in.
                    move=> [ind [is_spec' [e' [HIn' HEq']]]].
                    exists ind; split; trivial.
                    exists e'; split; trivial.
                    by constructor.
                }
                move=> [HInf Abs].
                destruct (leq_Cases _ _ HInf) as [HEq'|HSInf].
                {
                    destruct HEq'; rewrite Nat.eqb_refl in Abs.
                    specialize used_prop with (length eqns_hd) nil.
                    destruct used_prop as [_ []]; trivial.
                    split; trivial.
                    rewrite Nat.eqb_refl; move: Abs.
                    unfold partial_used_in.
                    move=> [ind [is_spec' [e' [HIn' HEq']]]].
                    rewrite cats0.
                    exists ind; split; trivial.
                    exists e'; split; trivial.
                    inversion HIn' as [H'|]; trivial.
                    destruct H'; move: is_spec'.
                    simpl in HEq'.
                    destruct HEq' as [Abs|[Abs _]]; inversion Abs.
                    move=> is_spec'.
                    apply list_rel_length in is_spec.
                    apply list_rel_length in is_spec'.
                    rewrite is_spec in is_spec'.
                    exfalso.
                    move: is_spec'; clear.
                    rewrite app_length; simpl.
                    induction (length path_in) as [|l HRec]; simpl.
                    by discriminate.
                    move=> H; apply HRec; inversion H as [H'].
                    do 2 rewrite <-H'; reflexivity.
                }
                {
                    case_eq (length eqns_hd =? pos).
                    all: move=> HEq'; rewrite HEq' in Abs.
                    {
                        rewrite Nat.eqb_eq in HEq'; destruct HEq'.
                        exfalso; apply (Nat.nle_succ_diag_l (length eqns_hd)).
                        apply/leP; trivial.
                    }
                    {
                        specialize used_prop with pos nil.
                        rewrite HEq' in used_prop.
                        destruct used_prop as [_ []]; trivial.
                        rewrite cats0; auto.
                    }
                }
            }
            {
                pose (pos := 0); fold pos; move: pos.
                induction len as [|len HRec]; simpl; trivial.
                move=> pos; specialize HRec with pos.+1.
                case_eq (List.existsb (Nat.eqb pos) (gen_range i1 i2)); simpl; auto.
                all: move=> Hmem; split; auto.
                {
                    apply H; trivial.
                    all: swap 1 2.
                    {
                        move=> pos' l'; rewrite <- app_assoc; simpl.
                        rewrite <-used_prop; split.
                        all: by move=> [].
                    }
                    clear HIn.
                    rewrite list_rel_last; split; trivial.
                    apply (SpecRange _ _ _ _ _ HEq1 HEq2).
                    rewrite List.existsb_exists in Hmem.
                    destruct Hmem as [x [LIn HEq]].
                    rewrite Nat.eqb_eq in HEq; destruct HEq.
                    rewrite gen_range_completeness in LIn; assumption.
                }
                move=> pos'; split.
                by move=> [].
                rewrite <- app_assoc; simpl.
                specialize used_prop with pos' (pos :: l').
                move=> [HInf Abs].
                destruct used_prop as [_ []].
                2: by idtac.
                split; trivial.
                destruct (_ =? _); trivial.
                move: Abs.
                unfold partial_used_in.
                move=> [ind [is_spec' [e' [HIn' HEq']]]].
                exists ind; split; trivial.
                exists e'; split; trivial.
                inversion HIn' as [H'|]; trivial.
                destruct H'; move: is_spec'.
                simpl in HEq'.
                destruct HEq' as [Abs|[Abs _]]; inversion Abs.
                move=> is_spec'.
                apply list_rel_length in is_spec.
                destruct (list_rel_append is_specialization path_nat path_in (pos :: l') (IRange ae1 ae2 :: path_tl)) as [H' _].
                move: H'; impl_tac; auto.
                move=> [_ H']; inversion H' as [|h1 h2 t1 t2 AbsRel].
                exfalso; rewrite <-not_true_iff_false in Hmem.
                apply Hmem; rewrite List.existsb_exists.
                eexists; split; [> idtac | exact (Nat.eqb_refl _)].
                inversion AbsRel as [| |ae1' ae2' i1' i2' i HEq1' HEq2'].
                rewrite HEq1 in HEq1'; inversion HEq1' as [HEq]; clear HEq1'; destruct HEq.
                rewrite HEq2 in HEq2'; inversion HEq2' as [HEq]; clear HEq2'; destruct HEq.
                rewrite gen_range_completeness; assumption.
            }
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            move=> v tree' H.
            destruct (_ && _); inversion H as [H']; clear H H' tree'.
            move: (HRec v next_tree); clear HRec.
            impl_tac; trivial; simpl.
            move=> H path_in path_nat is_spec HIn used_prop.
            move: (H (path_in ++ [:: ISlice aeL])); clear H.
            rewrite <- app_assoc; simpl.
            move=> H.
            split.
            {
                move=> pos; split.
                {
                    specialize used_prop with pos nil.
                    rewrite cats0 in used_prop.
                    split; destruct used_prop as [[H1 partial] _]; auto.
                    destruct (_ =? _); auto.
                    move: partial.
                    unfold partial_used_in.
                    move=> [ind [is_spec' [e' [HIn' HEq2]]]].
                    exists ind; split; trivial.
                    exists e'; split; trivial.
                    by constructor.
                }
                move=> [HInf Abs].
                destruct (leq_Cases _ _ HInf) as [HEq'|HSInf].
                {
                    destruct HEq'; rewrite Nat.eqb_refl in Abs.
                    specialize used_prop with (length eqns_hd) nil.
                    destruct used_prop as [_ []]; trivial.
                    split; trivial.
                    rewrite Nat.eqb_refl; move: Abs.
                    unfold partial_used_in.
                    move=> [ind [is_spec' [e' [HIn' HEq2]]]].
                    rewrite cats0.
                    exists ind; split; trivial.
                    exists e'; split; trivial.
                    inversion HIn' as [H'|]; trivial.
                    destruct H'; move: is_spec'.
                    simpl in HEq2.
                    destruct HEq2 as [Abs|[Abs _]]; inversion Abs.
                    move=> is_spec'.
                    apply list_rel_length in is_spec.
                    apply list_rel_length in is_spec'.
                    rewrite is_spec in is_spec'.
                    exfalso.
                    move: is_spec'; clear.
                    rewrite app_length; simpl.
                    induction (length path_in) as [|l HRec]; simpl.
                    by discriminate.
                    move=> H; apply HRec; inversion H as [H'].
                    do 2 rewrite <-H'; reflexivity.
                }
                {
                    case_eq (length eqns_hd =? pos).
                    all: move=> HEq'; rewrite HEq' in Abs.
                    {
                        rewrite Nat.eqb_eq in HEq'; destruct HEq'.
                        exfalso; apply (Nat.nle_succ_diag_l (length eqns_hd)).
                        apply/leP; trivial.
                    }
                    {
                        specialize used_prop with pos nil.
                        rewrite HEq' in used_prop.
                        destruct used_prop as [_ []]; trivial.
                        rewrite cats0; auto.
                    }
                }
            }
            {
                pose (pos := 0); fold pos; move: pos.
                induction len as [|len HRec]; simpl; trivial.
                move=> pos; specialize HRec with pos.+1.
                case_eq (List.existsb (Nat.eqb pos) iL); simpl; auto.
                all: move=> Hmem; split; auto.
                {
                    apply H; trivial.
                    all: swap 1 2.
                    {
                        move=> pos' l'; rewrite <- app_assoc; simpl.
                        rewrite <-used_prop; split.
                        all: by move=> [].
                    }
                    clear HIn.
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
                    rewrite list_rel_last; split; trivial.
                    apply (SpecSlice ae); trivial.
                }
                move=> pos'; split.
                by move=> [].
                rewrite <- app_assoc; simpl.
                specialize used_prop with pos' (pos :: l').
                move=> [HInf Abs].
                destruct used_prop as [_ []].
                2: by idtac.
                split; trivial.
                destruct (_ =? _); trivial.
                move: Abs.
                unfold partial_used_in.
                move=> [ind [is_spec' [e' [HIn' HEq2]]]].
                exists ind; split; trivial.
                exists e'; split; trivial.
                inversion HIn' as [H'|]; trivial.
                destruct H'; move: is_spec'.
                simpl in HEq2.
                destruct HEq2 as [Abs|[Abs _]]; inversion Abs.
                move=> is_spec'.
                apply list_rel_length in is_spec.
                destruct (list_rel_append is_specialization path_nat path_in (pos :: l') (ISlice aeL :: path_tl)) as [H' _].
                move: H'; impl_tac; auto.
                move=> [_ H']; inversion H' as [|h1 h2 t1 t2 AbsRel].
                inversion AbsRel as [|ae' aeL' i ListIn HEq'|].
                exfalso.
                move: HEq ListIn HEq' Hmem; clear; move: iL.
                induction aeL as [|hd tl HRec]; simpl.
                by move=> _ _ [].
                destruct fold_right as [l|].
                2: by idtac.
                move=> iL HEq [<-|HIn].
                {
                    move=> H; rewrite H in HEq; inversion HEq; simpl.
                    rewrite Nat.eqb_refl; simpl.
                    discriminate.
                }
                {
                    move=> eval_eq.
                    specialize HRec with l; move: HRec; impl_tac; trivial.
                    impl_tac; trivial.
                    impl_tac; trivial.
                    destruct (eval_arith_expr nil hd); inversion HEq; simpl.
                    destruct List.existsb.
                    {
                        rewrite orb_true_r; auto.
                    }
                    {
                        move=> H; exfalso; apply H; auto.
                    }
                }
            }
        }
    }
Qed.


Lemma partial_valid_use_tree'_add_expr:
    forall eqns_hd eqns_tl vars expr v path_in eL tree path_nat,
        partial_valid_use_tree' (length eqns_hd) eL v tree path_nat (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        length path_in < length path_nat ->
        partial_valid_use_tree' (length eqns_hd) (ExpVar (Index (Var v) path_in):: eL) v tree path_nat (eqns_hd ++ (vars, expr) :: eqns_tl).
Proof.
    move=> eqns_hd eqns_tl vars expr v path_in eL.
    refine (use_tree_find _ (fun trees => forall path_nat pos,
        partial_valid_list_use_tree' (length eqns_hd) eL v trees pos path_nat (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        length path_in < length path_nat ->
        partial_valid_list_use_tree' (length eqns_hd) (ExpVar (Index (Var v) path_in):: eL) v trees pos path_nat (eqns_hd ++ (vars, expr) :: eqns_tl)) _ _ _ _); simpl.
    {
        move=> uses _ path_nat partial_valid length_inf pos l'.
        rewrite partial_valid; clear partial_valid.
        destruct (_ =? _).
        all: split; move=> [HInf partial_def]; split; trivial.
        all: move: partial_def; unfold partial_used_in.
        all: move=> [ind [is_spec [e' [ListIn HEq]]]].
        all: exists ind; split; trivial; exists e'; split; trivial.
        by constructor.
        move: HEq; inversion ListIn as [H|]; trivial.
        destruct H; clear ListIn.
        move=> [H|[H _]]; move: length_inf is_spec; inversion H.
        clear.
        move=> length_inf length_eq.
        apply list_rel_length in length_eq.
        rewrite <-length_eq in length_inf; clear length_eq.
        rewrite app_length in length_inf.
        exfalso; move: length_inf.
        induction (length path_nat) as [|p HRec]; simpl.
        by idtac.
        move=> H; apply HRec.
        rewrite ltnS in H; assumption.
    }
    {
        move=> uses trees HRec path_nat [used valid] length_inf.
        split; auto.
        move=> pos; rewrite used; clear used.
        destruct (_ =? _); split; move=> [HInf partial]; split; trivial.
        all: move: partial; unfold partial_used_in.
        all: move=> [ind [is_spec [e' [HIn HEq]]]].
        all: exists ind; split; trivial.
        all: exists e'; split; trivial.
        by constructor.
        move: HEq; inversion HIn as [H|]; trivial; destruct H.
        move=> [H|[H _]]; move: is_spec length_inf; inversion H.
        clear.
        move=> length_eq; apply list_rel_length in length_eq; destruct length_eq.
        move=> H; exfalso; apply (Nat.nle_succ_diag_l (length path_nat)).
        apply/leP; assumption.
    }
    {
        trivial.
    }
    {
        move=> hd HRec_hd tl HRec_tl path_nat pos [valid_hd valid_tl] length_inf.
        split; auto.
        apply HRec_hd; auto.
        rewrite app_length; simpl; rewrite Nat.add_1_r.
        apply/leP.
        apply (Nat.le_trans _ (length path_nat)).
        by apply/leP.
        by apply Nat.le_succ_diag_r.
    }
Qed.

Lemma partial_valid_use_tree'_add_expr2:
    forall eqns_hd eqns_tl vars expr v eL tree path_in path_tl path_nat,
        partial_valid_use_tree' (length eqns_hd) eL v tree path_nat (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        length path_in = length path_nat ->
        (list_rel is_specialization path_nat path_in -> False) ->
        partial_valid_use_tree' (length eqns_hd) (ExpVar (Index (Var v) (path_in ++ path_tl)):: eL) v tree path_nat (eqns_hd ++ (vars, expr) :: eqns_tl).
Proof.
    move=> eqns_hd eqns_tl vars expr v eL.
    refine (use_tree_find _ (fun trees => forall path_in path_tl path_nat pos,
        partial_valid_list_use_tree' (length eqns_hd) eL v trees pos path_nat (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        length path_in = length path_nat ->
        (list_rel is_specialization path_nat path_in -> False) ->
        partial_valid_list_use_tree' (length eqns_hd) (ExpVar (Index (Var v) (path_in ++ path_tl)):: eL) v trees pos path_nat (eqns_hd ++ (vars, expr) :: eqns_tl))
            _ _ _ _); simpl.
    {
        move=> uses _ path_in path_tl path_nat valid length_eq not_spec pos l'.
        rewrite valid; clear valid.
        destruct (_ =? _); split; move=> [HInf partial]; split; trivial.
        all: move: partial; unfold partial_used_in.
        all: move=> [ind [is_spec [e' [ListIn HEq]]]].
        all: exists ind; split; trivial.
        all: exists e'; split; trivial.
        by constructor.
        inversion ListIn as [H|]; trivial; clear ListIn.
        destruct H; exfalso.
        apply not_spec; move: is_spec length_eq.
        destruct HEq as [H|[H _]]; inversion H.
        move=> list_rel_app length_eq.
        destruct (list_rel_append is_specialization path_nat path_in l' path_tl) as [[] _].
        all: auto.
    }
    {
        move=> uses trees HRec path_in path_tl path_nat [used valid] length_eq not_spec.
        split; auto.
        move=> pos; rewrite used; clear used.
        destruct (_ =? _); split; move=> [HInf partial]; split; trivial.
        all: move: partial; unfold partial_used_in.
        all: move=> [ind [is_spec [e' [ListIn HEq]]]].
        all: exists ind; split; trivial.
        all: exists e'; split; trivial.
        by constructor.
        inversion ListIn as [H|]; trivial; clear ListIn.
        destruct H; exfalso.
        apply not_spec; move: is_spec length_eq.
        destruct HEq as [H|[H _]]; inversion H.
        move=> list_rel_app length_eq.
        destruct (list_rel_append is_specialization path_nat path_in nil path_tl) as [[] _].
        by rewrite cats0.
        by assumption.
    }
    {
        trivial.
    }
    {
        move=> hd HRec_hd tl HRec_tl path_in path_tl path_nat pos [valid_hd valid_tl] length_eq not_spec.
        split; auto.
        clear HRec_tl valid_tl tl.
        destruct path_tl as [|ind path_tl].
        {
            rewrite cats0.
            clear HRec_hd.
            apply partial_valid_use_tree'_add_expr; auto.
            rewrite app_length; simpl.
            rewrite length_eq; rewrite Nat.add_1_r.
            apply/leP; apply Nat.le_refl.
        }
        {
            specialize HRec_hd with (path_in ++ [:: ind]) path_tl (path_nat ++ [:: pos]).
            repeat rewrite <- app_assoc in HRec_hd; simpl in HRec_hd.
            apply HRec_hd; auto.
            {
                do 2 rewrite app_length; auto.
            }
            {
                move=> H; apply list_rel_last in H; apply not_spec.
                destruct H; assumption.
            }
        }
    }
Qed.

Lemma partial_used_in_change_list:
    forall eL1 eL2,
        (forall v,
            (exists e, List.In e eL1 /\ Ensembles.In _ (expr_freefullvars e) v) <->
            (exists e, List.In e eL2 /\ Ensembles.In _ (expr_freefullvars e) v)) ->
        forall v path,
            partial_used_in v path eL1 <-> partial_used_in v path eL2.
Proof.
    move=> eL1 el2 equiv v path.
    unfold partial_used_in.
    split; move=> [ind [is_spec [e' [LIn EIn]]]].
    all: exists ind; split; trivial.
    all: destruct EIn as [EIn|[EIn HEmpty]].
    {
        specialize equiv with (Index (Var v) ind).
        destruct equiv as [[e []] _]; trivial.
        by exists e'.
        by exists e; auto.
    }
    {
        specialize equiv with (Var v).
        destruct equiv as [[e []] _]; trivial.
        by exists e'.
        by exists e; auto.
    }
    {
        specialize equiv with (Index (Var v) ind).
        destruct equiv as [_ [e []]]; trivial.
        by exists e'.
        by exists e; auto.
    }
    {
        specialize equiv with (Var v).
        destruct equiv as [_ [e []]]; trivial.
        by exists e'.
        by exists e; auto.
    }
Qed.

Lemma partial_valid_use_tree'_change_list:
    forall eL1 eL2,
        (forall v,
            (exists e, List.In e eL1 /\ Ensembles.In _ (expr_freefullvars e) v) <->
            (exists e, List.In e eL2 /\ Ensembles.In _ (expr_freefullvars e) v)) ->
        forall nb v eqns tree path,
            partial_valid_use_tree' nb eL1 v tree path eqns <->
            partial_valid_use_tree' nb eL2 v tree path eqns.
Proof.
    move=> eL1 eL2 equiv nb v eqns.
    pose (equiv' := partial_used_in_change_list _ _ equiv v).
    refine (use_tree_find _ (fun trees => forall pos path,
        partial_valid_list_use_tree' nb eL1 v trees pos path eqns <->
        partial_valid_list_use_tree' nb eL2 v trees pos path eqns) _ _ _ _); simpl.
    {
        move=> uses _ path.
        split; move=> H pos l'; rewrite H; clear H.
        all: destruct (_ =? _); split; move=> [H partial]; split; auto; move: partial.
        all: rewrite (equiv' (path ++ l')); trivial.
    }
    {
        move=> uses trees HRec path; split; move=> [H1 H2]; split; trivial.
        2,4: move: H2; rewrite HRec; trivial.
        all: move=> pos; rewrite H1; destruct (_ =? _); split; move=> [H p]; split; auto.
        all: move: p; rewrite equiv'; trivial.
    }
    {
        split; trivial.
    }
    {
        move=> hd HRec_hd tl HRec_tl pos path; split; move=>[]; split; auto.
        by rewrite <-HRec_hd; assumption.
        by rewrite <-HRec_tl; assumption.
        by rewrite HRec_hd; assumption.
        by rewrite HRec_tl; assumption.
    }
Qed.

Lemma update_use_tree_type_soundness:
    forall len_eqns_hd tree tree' path_tl typ,
        update_use_tree path_tl len_eqns_hd tree = Some tree' ->
        use_tree_of_type tree typ ->
        use_tree_of_type tree' typ.
Proof.
    move=> len_eqns_hd.
    refine (use_tree_find _ (fun trees => (forall path_tl typ pos indices trees',
        list_use_tree_of_type trees typ (utrees_length trees) ->
        update_use_trees pos path_tl len_eqns_hd trees indices = Some trees' ->
        list_use_tree_of_type trees' typ (utrees_length trees') /\
        utrees_length trees' = utrees_length trees) : Prop) _ _ _ _); simpl.
    {
        move=> uses typ tree' path_tl typ'.
        move=> H; apply build_use_tree_from_type_type_soundness in H.
        move=> ->; assumption.
    }
    {
        move=> uses trees HRec tree' [|path_hd path_tl] typ.
        all: destruct typ as [| |typ len].
        1,2,4,5: by move=> _ [].
        {
            move=> H trees_of_type; inversion H as [H']; clear H H' tree'; simpl.
            assumption.
        }
        move=> H type_of_trees; move: H.
        move: (HRec path_tl typ 0); clear HRec.
        simpl; move=> HRec.
        destruct path_hd as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i eval_eq | by idtac].
            move: (HRec [:: i]); clear HRec; move=> HRec.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            specialize HRec with trees'; move: HRec.
            impl_tac.
            by rewrite (list_use_tree_of_type_length _ _ _ type_of_trees).
            impl_tac; trivial.
            move=> [trees_of_type' length_eq].
            rewrite <-(list_use_tree_of_type_length _ _ _ type_of_trees).
            rewrite <-length_eq; assumption.
        }
        {
            case_eq (eval_arith_expr nil ae1); [> move=> i1 HEq1 | by idtac].
            case_eq (eval_arith_expr nil ae2); [> move=> i2 HEq2 | by idtac].
            move: (HRec (gen_range i1 i2)); clear HRec; move=> HRec; simpl.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move: (HRec trees'); clear HRec.
            impl_tac.
            by rewrite (list_use_tree_of_type_length _ _ _ type_of_trees); assumption.
            impl_tac; trivial.
            move=> [trees_of_type' length_eq].
            all: move=> H; inversion H as [H']; clear H H' tree'; simpl.
            rewrite <-(list_use_tree_of_type_length _ _ _ type_of_trees).
            rewrite <-length_eq; trivial.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            move: (HRec iL); clear HRec; move=> HRec; simpl.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move: (HRec trees'); clear HRec.
            impl_tac.
            by rewrite (list_use_tree_of_type_length _ _ _ type_of_trees); assumption.
            impl_tac; trivial.
            move=> [trees_of_type' length_eq].
            all: move=> H; inversion H as [H']; clear H H' tree'; simpl.
            rewrite <-(list_use_tree_of_type_length _ _ _ type_of_trees).
            rewrite <-length_eq; trivial.
        }
    }
    {
        move=> path_tl typ pos indices trees' _ H.
        destruct (_ && _); inversion H; simpl; auto.
    }
    {
        move=> hd HRec_hd tl HRec_tl path_tl typ pos indices trees' [type_of_hd type_of_tl].
        move: (HRec_tl path_tl typ (pos + 1) indices); clear HRec_tl.
        destruct update_use_trees as [trees'1|]; [> simpl | by idtac ].
        move=> H; move: (H trees'1); clear H.
        impl_tac; trivial.
        impl_tac; trivial.
        move=> [type_of_tl' length_eq].
        destruct List.existsb; move=> HEq.
        {
            case_eq (update_use_tree path_tl len_eqns_hd hd).
            2: by move=> H; rewrite H in HEq; discriminate.
            move=> hd' H; rewrite H in HEq.
            inversion HEq as [H']; clear HEq H' trees'; simpl.
            split; [> split; auto | auto].
            specialize HRec_hd with hd' path_tl typ; move: HRec_hd.
            impl_tac; trivial.
            impl_tac; trivial.
        }
        {
            inversion HEq as [H']; clear HEq H' trees'; simpl.
            split; [> split; auto | auto].
        }
    }
Qed.

Lemma update_use_tree_subtree:
    forall len_eqns_hd tree tree' path_tl,
        update_use_tree path_tl len_eqns_hd tree = Some tree' ->
        sub_utree tree tree'.
Proof.
    move=> len_eqns_hd.
    refine (use_tree_find _ (fun trees => (forall path_tl pos indices trees',
        update_use_trees pos path_tl len_eqns_hd trees indices = Some trees' ->
        sub_utrees trees trees') : Prop) _ _ _ _); simpl.
    {
        move=> uses typ tree' path_tl HEq.
        constructor.
    }
    {
        move=> uses trees HRec tree' [|path_hd path_tl].
        {
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            constructor; clear.
            induction trees; constructor; [> exact (sub_utree_refl _) | assumption ].
        }
        move: (HRec path_tl 0); clear HRec.
        simpl; move=> HRec.
        destruct path_hd as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i eval_eq | by idtac].
            move: (HRec [:: i]); clear HRec; move=> HRec.
            destruct update_use_trees as [trees'|].
            all: move=> H; inversion H as [H']; clear H H' tree'; simpl.
            move: (HRec trees' Logic.eq_refl); clear HRec; move=> H.
            constructor; assumption.
        }
        {
            case_eq (eval_arith_expr nil ae1); [> move=> i1 HEq1 | by idtac].
            case_eq (eval_arith_expr nil ae2); [> move=> i2 HEq2 | by idtac].
            move: (HRec (gen_range i1 i2)); clear HRec; move=> HRec; simpl.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move: (HRec _ Logic.eq_refl); clear HRec; move=> partial_valid.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            constructor; assumption.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            move: (HRec iL); clear HRec; move=> HRec; simpl.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move: (HRec _ Logic.eq_refl); clear HRec; move=> partial_valid.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            constructor; assumption.
        }
    }
    {
        move=> path_tl pos indices trees' H.
        destruct (_ && _); inversion H; constructor.
    }
    {
        move=> hd HRec_hd tl HRec_tl path_tl pos indices trees'.
        move: (HRec_tl path_tl (pos + 1) indices); clear HRec_tl.
        destruct update_use_trees as [trees'1|]; [> simpl | by idtac ].
        move=> H; move: (H trees'1); clear H.
        impl_tac; trivial.
        move=> HRec_tl HEq.
        destruct List.existsb.
        2: inversion HEq; constructor; [> exact (sub_utree_refl _) | assumption ].
        case_eq (update_use_tree path_tl len_eqns_hd hd).
        2: by move=> H; rewrite H in HEq; discriminate.
        move=> hd' update_eq; rewrite update_eq in HEq.
        inversion HEq as [H']; clear HEq H' trees'; simpl.
        apply HRec_hd in update_eq.
        constructor; assumption.
    }
Qed.

Lemma update_use_tree_access:
    forall len_eqns_hd tree tree' path_tl,
        update_use_tree path_tl len_eqns_hd tree = Some tree' ->
        valid_utree_access tree' path_tl.
Proof.
    move=> len_eqns_hd.
    refine (use_tree_find _ (fun trees => (forall path_tl pos indices trees',
        update_use_trees pos path_tl len_eqns_hd trees indices = Some trees' ->
        indices <> nil /\
        Forall (fun i => i < pos + utrees_length trees') indices /\
        valid_utrees_access trees' pos indices path_tl) : Prop) _ _ _ _); simpl.
    {
        move=> uses typ tree' path_tl HEq.
        exact (build_use_tree_from_type_access _ _ _ _ _ HEq).
    }
    {
        move=> uses trees HRec tree' [|path_hd path_tl].
        {
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            constructor.
        }
        move: (HRec path_tl 0); clear HRec.
        simpl; move=> HRec.
        destruct path_hd as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i eval_eq | by idtac].
            move: (HRec [:: i]); clear HRec; move=> HRec.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            rewrite eval_eq.
            move: (HRec _ Logic.eq_refl); clear HRec; move=> HRec.
            rewrite add0n in HRec; assumption.
        }
        {
            case_eq (eval_arith_expr nil ae1); [> move=> i1 HEq1 | by idtac].
            case_eq (eval_arith_expr nil ae2); [> move=> i2 HEq2 | by idtac].
            move: (HRec (gen_range i1 i2)); clear HRec; move=> HRec; simpl.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move: (HRec _ Logic.eq_refl); clear HRec; move=> partial_valid.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            rewrite HEq1; rewrite HEq2.
            rewrite add0n in partial_valid; assumption.
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            move: (HRec iL); clear HRec; move=> HRec; simpl.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move: (HRec _ Logic.eq_refl); clear HRec; move=> partial_valid.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            rewrite HEq.
            rewrite add0n in partial_valid; assumption.
        }
    }
    {
        move=> path_tl pos indices trees' H.
        case_eq (forallb (Nat.ltb^~pos) indices && List.existsb xpredT indices).
        all: move=> HEq; rewrite HEq in H; inversion H; simpl; auto.
        move/andP in HEq; unfold is_true in HEq; destruct HEq as [all_inf not_empty].
        repeat split.
        {
            move=> H'; rewrite H' in not_empty; simpl in not_empty; discriminate.
        }
        {
            rewrite Forall_forall; rewrite List.forallb_forall in all_inf.
            move=> x LIn; apply all_inf in LIn.
            rewrite addn0; rewrite Nat.ltb_lt in LIn.
            apply/ltP; assumption.
        }
    }
    {
        move=> hd HRec_hd tl HRec_tl path_tl pos indices trees'.
        move: (HRec_tl path_tl (pos + 1) indices); clear HRec_tl.
        destruct update_use_trees as [trees'1|]; [> simpl | by idtac ].
        move=> H; move: (H trees'1); clear H.
        impl_tac; trivial.
        move=> HRec_tl HEq.
        rewrite addn1 in HRec_tl.
        case_eq (List.existsb (Nat.eqb pos) indices); move=> Hmem; rewrite Hmem in HEq.
        {
            case_eq (update_use_tree path_tl len_eqns_hd hd).
            2: by move=> H; rewrite H in HEq; discriminate.
            move=> hd' update_eq; rewrite update_eq in HEq.
            inversion HEq as [H']; clear HEq H' trees'; simpl.
            rewrite Hmem.
            rewrite addnS; rewrite addSn in HRec_tl.
            destruct HRec_tl as [H1 [H2 H3]]; repeat split; trivial.
            apply HRec_hd; assumption.
        }
        {
            inversion HEq as [H']; clear HEq H' trees'; simpl.
            rewrite Hmem.
            rewrite addnS; rewrite addSn in HRec_tl.
            destruct HRec_tl as [H1 [H2 H3]]; repeat split; trivial.
        }
    }
Qed.

Lemma update_use_tree_soundness:
    forall eqns_hd eqns_tl vars expr v eL tree tree' path_nat path_in path_tl,
        update_use_tree path_tl (length eqns_hd) tree = Some tree' ->
        (partial_valid_use_tree' (length eqns_hd) eL v tree path_nat (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        list_rel is_specialization path_nat path_in ->
        is_subexpr (ExpVar (Index (Var v) (path_in ++ path_tl))) expr ->
        partial_valid_use_tree' (length eqns_hd) (ExpVar (Index (Var v) (path_in ++ path_tl)) :: eL) v tree' path_nat (eqns_hd ++ (vars, expr) :: eqns_tl)).
Proof.
    move=> eqns_hd eqns_tl vars expr v eL.
    refine (use_tree_find _ (fun trees => (forall path_tl pos indices trees',
        update_use_trees pos path_tl (length eqns_hd) trees indices = Some trees' ->
        (forall ind path_in path_nat,
            partial_valid_list_use_tree' (length eqns_hd) eL v trees pos path_nat
            (eqns_hd ++ (vars, expr) :: eqns_tl) ->
            length path_nat = length path_in ->
            (forall i, List.existsb (Nat.eqb i) indices <-> list_rel is_specialization (path_nat ++ [:: i]) (path_in ++ [:: ind])) ->
            is_subexpr (ExpVar (Index (Var v) (path_in ++ ind :: path_tl))) expr ->
            partial_valid_list_use_tree' (length eqns_hd) (ExpVar (Index (Var v) (path_in ++ ind :: path_tl)) :: eL) v trees' pos path_nat (eqns_hd ++ (vars, expr) :: eqns_tl)
            )) : Prop) _ _ _ _); simpl.
    {
        move=> uses typ tree' path_nat path_in path_tl tree_of_type HEq.
        move: (build_use_tree_from_type_soundness path_tl vars eqns_hd eqns_tl expr eL uses typ v tree').
        impl_tac; trivial.
        move=> soundness.
        specialize soundness with path_in path_nat.
        move=> is_spec is_sub.
        move: soundness; impl_tac; trivial.
        impl_tac; trivial.
        impl_tac; trivial.
    }
    {
        move=> uses trees HRec tree' path_nat path_in [|path_hd path_tl].
        {
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            move=> [HForall valid_list] is_spec HIn.
            split.
            {
                move=> pos; split.
                {
                    move=> [<-|ListIn].
                    {
                        split; auto.
                        rewrite Nat.eqb_refl.
                        unfold partial_used_in.
                        eexists; split.
                        by exact is_spec.
                        eexists; split.
                        by constructor 1.
                        rewrite cats0; left; constructor.
                    }
                    {
                        rewrite HForall in ListIn.
                        destruct ListIn as [HInf used]; split; trivial.
                        destruct (_ =? _); trivial.
                        unfold partial_used_in; unfold partial_used_in in used.
                        destruct used as [ind [is_spec' [e' [HIn' HEq']]]].
                        exists ind; split; trivial.
                        exists e'; split; trivial.
                        by constructor.
                    }
                }
                {
                    move=> [HInf used].
                    destruct (leq_Cases _ _ HInf) as [HEq|HInf']; auto.
                    right; rewrite HForall.
                    split; trivial.
                    assert (length eqns_hd =? pos = false) as HEq.
                    {
                        rewrite <- not_true_iff_false; rewrite Nat.eqb_eq.
                        move=> H; destruct H.
                        apply (Nat.nle_succ_diag_l (length eqns_hd)).
                        apply/leP; assumption.
                    }
                    rewrite HEq in used; rewrite HEq; trivial.
                }
            }
            {
                clear HRec.
                move: valid_list.
                rewrite cats0; rewrite cats0 in HIn.
                pose (pos := 0); fold pos; move: pos.
                induction trees as [|hd tl HRec]; simpl in *; trivial.
                move=> pos [valid_hd valid_tl]; split; auto.
                apply partial_valid_use_tree'_add_expr; trivial.
                rewrite app_length; simpl; rewrite Nat.add_1_r.
                apply list_rel_length in is_spec; rewrite is_spec.
                apply/leP.
                apply Nat.le_refl.
            }
        }
        move: (HRec path_tl 0); clear HRec.
        simpl; move=> HRec.
        destruct path_hd as [ae|ae1 ae2|aeL].
        {
            case_eq (eval_arith_expr nil ae); [> move=> i eval_eq | by idtac].
            move: (HRec [:: i]); clear HRec; move=> HRec.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move=> H; inversion H as [H']; clear H H' tree'; simpl.
            move: (HRec trees' Logic.eq_refl); clear HRec; move=> H.
            move=> [HForall partial_valid] is_spec HIn.
            split.
            {
                move=> pos; rewrite HForall.
                destruct (_ =? _); auto.
                all: split; move=> [H1 H2]; split; trivial; move: H2.
                all: unfold partial_used_in; move=> [ind [is_spec' [e' [ListIn HEq]]]].
                all: exists ind; split; trivial; exists e'; split; trivial.
                by constructor.
                move: HEq; inversion ListIn as [H0|]; trivial.
                destruct H0; clear ListIn.
                move=> [HEq|[HEq _]]; exfalso; move: is_spec'; inversion HEq.
                move: is_spec; clear.
                intros H H'.
                apply list_rel_length in H.
                destruct (list_rel_append is_specialization path_nat path_in nil (IInd ae :: path_tl)) as [[_ H2] _].
                by rewrite cats0.
                apply list_rel_length in H2; simpl in H2; discriminate.
            }
            apply (H (IInd ae) path_in path_nat) in partial_valid; simpl; auto; clear H.
            {
                apply list_rel_length in is_spec; assumption.
            }
            {
                move=> i'; rewrite orb_false_r.
                split; move=> H.
                {
                    unfold is_true in H; rewrite Nat.eqb_eq in H; destruct H.
                    rewrite list_rel_last; split; trivial.
                    constructor; trivial.
                }
                {
                    apply list_rel_last in H; destruct H as [_ H].
                    inversion H as [ae' i2 HEq'| |].
                    rewrite eval_eq in HEq'.
                    inversion HEq'; apply Nat.eqb_refl.
                }
            }
        }
        {
            case_eq (eval_arith_expr nil ae1); [> move=> i1 HEq1; simpl | discriminate ].
            case_eq (eval_arith_expr nil ae2); [> move=> i2 HEq2; simpl | discriminate ].
            move: (HRec (gen_range i1 i2)); clear HRec; move=> HRec; simpl.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move: (HRec _ Logic.eq_refl); clear HRec; move=> partial_valid.
            all: move=> H; inversion H as [H']; clear H H' tree'; simpl.
            specialize partial_valid with (IRange ae1 ae2) path_in path_nat.
            move=> [HForall pvalid] is_spec is_sub; split.
            {
                move=> pos; rewrite HForall.
                split; move=> [HInf H]; split; trivial; move: H.
                all: destruct (_ =? _); trivial.
                all: unfold partial_used_in; move=> [ind [is_spec' [e' [ListIn HEq']]]].
                all: exists ind; split; trivial.
                all: exists e'; split; trivial.
                by constructor.
                move: HEq'; inversion ListIn as [H0|]; trivial.
                destruct H0; clear ListIn.
                move=> [HEq'|[HEq' _]]; exfalso; move: is_spec'; inversion HEq'.
                move: is_spec; clear.
                intros H H'.
                apply list_rel_length in H.
                destruct (list_rel_append is_specialization path_nat path_in nil (IRange ae1 ae2 :: path_tl)) as [[_ H2] _].
                by rewrite cats0.
                apply list_rel_length in H2; simpl in H2; discriminate.
            }
            {
                apply partial_valid; trivial.
                by apply list_rel_length in is_spec.
                move=> pos; split.
                {
                    move=> Hmem.
                    rewrite list_rel_last; split; auto.
                    apply (SpecRange _ _ _ _ _ HEq1 HEq2).
                    unfold is_true in Hmem; rewrite List.existsb_exists in Hmem.
                    destruct Hmem as [x [LIn HEq]].
                    rewrite Nat.eqb_eq in HEq; destruct HEq.
                    rewrite gen_range_completeness in LIn; assumption.
                }
                {
                    move=> H; apply list_rel_last in H; destruct H as [_ H].
                    inversion H as [| |ae1' ae2' i1' i2' i HEq1' HEq2'].
                    rewrite HEq1 in HEq1'; inversion HEq1' as [H']; clear HEq1'; destruct H'.
                    rewrite HEq2 in HEq2'; inversion HEq2' as [H']; clear HEq2'; destruct H'.
                    unfold is_true; rewrite List.existsb_exists.
                    eexists; split; [> idtac | exact (Nat.eqb_refl _)].
                    rewrite gen_range_completeness; assumption.
                }
            }
        }
        {
            case_eq (fold_right
            (fun ae (l : option (seq nat)) => match l with
                | Some l' => match eval_arith_expr nil ae with | Some i => Some (i :: l') | None => None end
                | None => None end) (Some [::]) aeL)
            ; [> move=> iL HEq; simpl | by idtac].
            move: (HRec iL); clear HRec; move=> HRec; simpl.
            destruct update_use_trees as [trees'|].
            2: by idtac.
            move: (HRec _ Logic.eq_refl); clear HRec; move=> partial_valid.
            all: move=> H; inversion H as [H']; clear H H' tree'; simpl.
            specialize partial_valid with (ISlice aeL) path_in path_nat.
            move=> [HForall pvalid] is_spec is_sub; split.
            {
                move=> pos; rewrite HForall.
                split; move=> [HInf H]; split; trivial; move: H.
                all: destruct (_ =? _); trivial.
                all: unfold partial_used_in; move=> [ind [is_spec' [e' [ListIn HEq']]]].
                all: exists ind; split; trivial.
                all: exists e'; split; trivial.
                by constructor.
                move: HEq'; inversion ListIn as [H0|]; trivial.
                destruct H0; clear ListIn.
                move=> [HEq'|[HEq' _]]; exfalso; move: is_spec'; inversion HEq'.
                move: is_spec; clear.
                intros H H'.
                apply list_rel_length in H.
                destruct (list_rel_append is_specialization path_nat path_in nil (ISlice aeL :: path_tl)) as [[_ H2] _].
                by rewrite cats0.
                apply list_rel_length in H2; simpl in H2; discriminate.
            }
            {
                apply partial_valid; trivial.
                by apply list_rel_length in is_spec.
                move=> pos; split.
                {
                    move=> Hmem.
                    rewrite list_rel_last; split; auto.
                    move: Hmem HEq; clear.
                    move=> Hmem HEq.
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
                    move=> H; apply list_rel_last in H; destruct H as [_ H].
                    inversion H as [|ae aeL' i ListIn eval_eq|].
                    move: eval_eq HEq ListIn; clear.
                    move=> eval_eq; move: iL.
                    induction aeL as [|hd tl HRec]; simpl.
                    by idtac.
                    move=> iL; destruct fold_right as [iL'|].
                    2: by idtac.
                    move=> eval_eq' [HEq|HIn].
                    {
                        destruct HEq.
                        rewrite eval_eq in eval_eq'; inversion eval_eq'; simpl.
                        rewrite Nat.eqb_refl; auto.
                    }
                    {
                        destruct (eval_arith_expr nil hd); inversion eval_eq'; simpl.
                        rewrite HRec; auto.
                        rewrite orb_true_r; trivial.
                    }
                }
            }
        }
    }
    {
        move=> path_tl pos indices trees' H.
        destruct (_ && _); inversion H; simpl; auto.
    }
    {
        move=> hd HRec_hd tl HRec_tl path_tl pos indices trees'.
        move: (HRec_tl path_tl (pos + 1) indices); clear HRec_tl.
        destruct update_use_trees as [trees'1|]; [> simpl | by idtac ].
        move=> H; move: (H trees'1); clear H.
        impl_tac; trivial.
        move=> HRec_tl HEq.
        move=> ind path_in path_nat [pvalid_hd pvalid_tl] length_eq' is_spec is_sub.
        specialize HRec_tl with ind path_in path_nat; move: HRec_tl.
        rewrite addn1.
        do 4 (impl_tac; trivial).
        move=> valid_tl.
        case_eq (List.existsb (Nat.eqb pos) indices); move=> Hmem; rewrite Hmem in HEq.
        {
            case_eq (update_use_tree path_tl (length eqns_hd) hd).
            2: by move=> H; rewrite H in HEq; discriminate.
            move=> hd' update_eq; rewrite update_eq in HEq.
            inversion HEq as [H']; clear HEq H' trees'; simpl.
            split; trivial.
            specialize HRec_hd with hd' (path_nat ++ [:: pos]) (path_in ++ [:: ind]) path_tl.
            move: HRec_hd; do 2 (impl_tac; trivial).
            impl_tac.
            by rewrite <-is_spec; rewrite Hmem; auto.
            rewrite <-app_assoc; simpl.
            impl_tac; trivial.
        }
        {
            inversion HEq as [H']; clear HEq H' trees'; simpl.
            split; trivial.
            move: (partial_valid_use_tree'_add_expr2 eqns_hd eqns_tl vars expr v eL hd (path_in ++ [:: ind]) path_tl (path_nat ++ [:: pos])).
            rewrite <- app_assoc; simpl.
            move=> H; apply H; clear H; trivial.
            {
                do 2 rewrite app_length; simpl; rewrite length_eq'; reflexivity.
            }
            {
                rewrite <-is_spec; rewrite Hmem.
                discriminate.
            }
        }
    }
Qed.

Lemma partial_valid_use_tree_change_name:
    forall ctxt eqns_hd eqns_tl var ident expr vars path_in tree,
        get_ident var <> ident ->
        partial_valid_use_tree' (length eqns_hd) ctxt ident tree path_in (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_use_tree' (length eqns_hd) (ExpVar var :: ctxt) ident tree path_in (eqns_hd ++ (vars, expr) :: eqns_tl).
Proof.
    move=> ctxt eqns_hd eqns_tl var ident expr vars path_in tree ident_diff.
    move: tree path_in.
    refine (use_tree_find _ (fun trees => forall pos path_in,
        partial_valid_list_use_tree' (length eqns_hd) ctxt ident trees pos path_in (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_list_use_tree' (length eqns_hd) (ExpVar var :: ctxt) ident trees pos path_in (eqns_hd ++ (vars, expr) :: eqns_tl)
        ) _ _ _ _).
    {
        move=> uses typ path_in; simpl.
        move=> equiv pos l'; rewrite equiv.
        split; move=> [HInf partial]; split; trivial.
        all: move: partial; destruct (_ =? _); trivial.
        all: unfold partial_used_in; move=> [ind [is_spec [e' [LIn HEq]]]].
        all: exists ind; split; trivial.
        all: exists e'; split; trivial.
        by constructor.
        inversion LIn as [HEq'|]; trivial.
        destruct HEq'; simpl in HEq.
        exfalso; apply ident_diff.
        destruct HEq as [Abs|[Abs _]]; inversion Abs; simpl; reflexivity.
    }
    {
        simpl.
        move=> use trees HRec path_in [partial_used partial_valid].
        split; trivial.
        {
            clear HRec partial_valid.
            move=> pos; rewrite partial_used; clear partial_used.
            split; move=> [HInf partial]; split; trivial.
            all: move: partial; destruct (_ =? _); trivial.
            all: unfold partial_used_in; move=> [ind [is_spec [e' [LIn HEq]]]].
            all: exists ind; split; trivial.
            all: exists e'; split; trivial.
            by constructor.
            inversion LIn as [HEq'|]; trivial.
            destruct HEq'; simpl in HEq.
            exfalso; apply ident_diff.
            destruct HEq as [Abs|[Abs _]]; inversion Abs; simpl; reflexivity.
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

Lemma partial_valid_use_tree_Var:
    forall ctxt eqns_hd eqns_tl v ident expr vars path_in tree,
        0 < length path_in ->
        partial_valid_use_tree' (length eqns_hd) ctxt ident tree path_in (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_use_tree' (length eqns_hd) (ExpVar (Var v) :: ctxt) ident tree path_in (eqns_hd ++ (vars, expr) :: eqns_tl).
Proof.
    move=> ctxt eqns_hd eqns_tl v ident expr vars path_in tree.
    move: tree path_in.
    refine (use_tree_find _ (fun trees => forall pos path_in,
        0 < length path_in ->
        partial_valid_list_use_tree' (length eqns_hd) ctxt ident trees pos path_in (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_list_use_tree' (length eqns_hd) (ExpVar (Var v) :: ctxt) ident trees pos path_in (eqns_hd ++ (vars, expr) :: eqns_tl)
        ) _ _ _ _).
    {
        move=> uses typ path_in; simpl.
        move=> inf_length equiv pos l'; rewrite equiv.
        split; move=> [HInf partial]; split; trivial.
        all: move: partial; destruct (_ =? _); trivial.
        all: unfold partial_used_in; move=> [ind [is_spec [e' [LIn HEq]]]].
        all: exists ind; split; trivial.
        all: exists e'; split; trivial.
        by constructor.
        inversion LIn as [HEq'|]; trivial.
        destruct HEq'; simpl in HEq.
        destruct HEq as [Abs|[Abs HNeq]]; [> inversion Abs | rewrite HNeq in is_spec ].
        inversion is_spec.
        by destruct path_in; simpl in *.
    }
    {
        simpl.
        move=> use trees HRec path_in inf_length [partial_used partial_valid].
        split; trivial.
        {
            clear HRec partial_valid.
            move=> pos; rewrite partial_used; clear partial_used.
            split; move=> [HInf partial]; split; trivial.
            all: move: partial; destruct (_ =? _); trivial.
            all: unfold partial_used_in; move=> [ind [is_spec [e' [LIn HEq]]]].
            all: exists ind; split; trivial.
            all: exists e'; split; trivial.
            by constructor.
            inversion LIn as [HEq'|]; trivial.
            destruct HEq'; simpl in HEq.
            destruct HEq as [Abs|[Abs HNeq]]; [> inversion Abs | rewrite HNeq in is_spec ].
            inversion is_spec.
            by destruct path_in; simpl in *.
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
        move=> tree HRec_hd trees HRec_tl pos path_in inf_length [valid_hd valid_tl].
        split; auto.
        apply HRec_hd; trivial.
        rewrite app_length; simpl; rewrite Nat.add_1_r.
        by constructor.
    }
Qed.

Lemma valid_access_keep_lemma_utree:
    forall ind typ path trees pos,
        valid_utrees_access trees pos ind path ->
        list_use_tree_of_type trees typ (utrees_length trees) ->
        (exists i, List.In i ind /\ i >= pos /\ i < pos + utrees_length trees) ->
        exists t,
            valid_utree_access t path /\ use_tree_of_type t typ.
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
                rewrite addnS in HSup.
                rewrite addSn; assumption.
            }
        }
    }
Qed.

Lemma valid_access_keep_utree:
    forall ind tree typ,
        valid_utree_access tree ind ->
        use_tree_of_type tree typ ->
        valid_access typ ind.
Proof.
    move=> ind; induction ind as [|ind tl HRec].
    {
        move=> tree [|d m|typ len]; simpl; trivial.
    }
    {
        move=> [uses b|uses trees] typ; simpl.
        by move=> H; inversion H.
        destruct typ as [| |typ len].
        1,2: by move=> _ [].
        simpl; destruct ind as [ae|ae1 ae2|aeL].
        {
            unfold eval_lt.
            destruct eval_arith_expr.
            2: by move=> [].
            move=> [H0 [H1 H2]] trees_of_type.
            inversion H1; rewrite <-(list_use_tree_of_type_length _ _ _ trees_of_type).
            split; trivial.
            destruct (valid_access_keep_lemma_utree [:: n] typ tl trees 0) as [t [valid of_type]].
            by assumption.
            by rewrite (list_use_tree_of_type_length _ _ _ trees_of_type); assumption.
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
            rewrite <-(list_use_tree_of_type_length _ _ _ trees_of_type).
            split.
            {
                destruct (valid_access_keep_lemma_utree _ typ _ _ _ H2) as [t [valid of_type]].
                by rewrite (list_use_tree_of_type_length _ _ _ trees_of_type); assumption.
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
            move=> iL HEq [NotEmpty [AllInf valid_acc]] type_of; split; [> idtac | split ].
            {
                destruct (valid_access_keep_lemma_utree _ typ _ _ _ valid_acc) as [t [valid of_type]].
                by rewrite (list_use_tree_of_type_length _ _ _ type_of); assumption.
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
                rewrite <-(list_use_tree_of_type_length _ _ _ type_of).
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

Lemma valid_var_utree_keep:
    forall v dep1 dep2,
        map fst dep1 = map fst dep2 ->
        list_rel sub_utree (map snd dep1) (map snd dep2) ->
        valid_var_utree dep1 v ->
        valid_var_utree dep2 v.
Proof.
    move=> v; destruct v as [v|[v|]ind]; simpl.
    3: by do 3 intro; move=> [].
    all: move=> dep1; induction dep1 as [|[k1 v1] t1 HRec]; simpl.
    all: move=> [|[k2 v2] t2] H; simpl in *; inversion H.
    1,3: move=> _ H'; exact H'.
    all: move=> lr; inversion lr; destruct ident_beq.
    by move=> _; discriminate.
    by apply HRec; assumption.
    by move=> valid; refine (sub_utree_keep_access _ _ _ valid _); assumption.
    by apply HRec; assumption.
Qed.


Lemma partial_valid_use_tree_add_prim:
    forall eqns_hd eqns_tl vars expr v t path,
        partial_valid_use_tree (length eqns_hd).+1 v t path (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_use_tree' (length eqns_hd) nil v t path (eqns_hd ++ (vars, expr) :: eqns_tl).
Proof.
    move=> eqns_hd eqns_tl vars expr v.
    refine (use_tree_find _ (fun trees => forall path pos,
        partial_valid_list_use_tree (length eqns_hd).+1 v trees pos path (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_list_use_tree' (length eqns_hd) nil v trees pos path (eqns_hd ++ (vars, expr) :: eqns_tl)
    ) _ _ _ _).
    {
        move=> use typ path; simpl.
        move=> equiv pos l'; rewrite equiv; clear equiv.
        split.
        {
            move=> [HInf used].
            split.
            by apply ltnW.
            case_eq (length eqns_hd =? pos); trivial.
            rewrite Nat.eqb_eq; move=> H; destruct H.
            exfalso.
            refine (Nat.nle_succ_diag_l _ _).
            apply/leP.
            exact HInf.
        }
        {
            case_eq (length eqns_hd =? pos).
            {
                move=> _ [_ Abs]; exfalso; move: Abs.
                unfold partial_used_in; simpl.
                by move=> [ind [_ [e' [[] _]]]].
            }
            {
                rewrite <-not_true_iff_false; rewrite Nat.eqb_eq.
                move=> HNeq [HInf used]; split; trivial.
                destruct (leq_Cases _ _ HInf); auto.
            }
        }
    }
    {
        simpl.
        move=> uses trees HRec path [used partial_used].
        split; auto.
        move=> pos; rewrite used; clear used.
        clear.
        split.
        {
            move=> [HInf used].
            split.
            by apply ltnW.
            case_eq (length eqns_hd =? pos); trivial.
            rewrite Nat.eqb_eq; move=> H; destruct H.
            exfalso.
            refine (Nat.nle_succ_diag_l _ _).
            apply/leP.
            exact HInf.
        }
        {
            case_eq (length eqns_hd =? pos).
            {
                move=> _ [_ Abs]; exfalso; move: Abs.
                unfold partial_used_in; simpl.
                by move=> [ind [_ [e' [[] _]]]].
            }
            {
                rewrite <-not_true_iff_false; rewrite Nat.eqb_eq.
                move=> HNeq [HInf used]; split; trivial.
                destruct (leq_Cases _ _ HInf); auto.
            }
        }
    }
    {
        simpl; trivial.
    }
    {
        simpl.
        move=> tree_hd HRec_hd trees HRec_tl path pos [valid_hd valid_tl]; auto.
    }
Qed.

Lemma partial_valid_use_tree_remove_prim:
    forall eqns_hd eqns_tl vars expr v t path,
        partial_valid_use_tree' (length eqns_hd) [:: expr] v t path (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_use_tree (length eqns_hd) v t path (eqns_hd ++ (vars, expr) :: eqns_tl).
Proof.
    move=> eqns_hd eqns_tl vars expr v.
    refine (use_tree_find _ (fun trees => forall path pos,
        partial_valid_list_use_tree' (length eqns_hd) [:: expr] v trees pos path (eqns_hd ++ (vars, expr) :: eqns_tl) ->
        partial_valid_list_use_tree (length eqns_hd) v trees pos path (eqns_hd ++ (vars, expr) :: eqns_tl)
    ) _ _ _ _).
    {
        move=> uses typ path; simpl.
        move=> equiv pos l'; rewrite equiv; clear equiv.
        split; move=> [HInf used]; split; trivial.
        {
            case_eq (length eqns_hd =? pos); move=> HEq; rewrite HEq in used; trivial.
            move: used.
            rewrite Nat.eqb_eq in HEq; rewrite <-HEq.
            unfold partial_used_in; unfold used_in; clear.
            move=> [ind [is_spec [e' [LIn HEq]]]].
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            exists vars; exists expr; exists ind; repeat split; trivial.
            by inversion LIn as [HEq'|LIn']; [> destruct HEq' | inversion LIn' ].
        }
        {
            case_eq (length eqns_hd =? pos); trivial.
            rewrite Nat.eqb_eq; move=> H; destruct H.
            move: used.
            unfold partial_used_in; unfold used_in; clear.
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            move=> [vL [e [ind [HEq [is_spec HIn]]]]].
            exists ind; split; trivial.
            exists expr; split; auto.
            move: HIn; inversion HEq; trivial.
        }
    }
    {
        simpl.
        move=> uses trees HRec path [equiv pvalid]; split; auto.
        move=> pos; rewrite equiv; clear equiv.
        split; move=> [HInf used]; split; trivial.
        {
            case_eq (length eqns_hd =? pos); move=> HEq; rewrite HEq in used; trivial.
            move: used.
            rewrite Nat.eqb_eq in HEq; rewrite <-HEq.
            unfold partial_used_in; unfold used_in; clear.
            move=> [ind [is_spec [e' [LIn HEq]]]].
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            exists vars; exists expr; exists ind; repeat split; trivial.
            by inversion LIn as [HEq'|LIn']; [> destruct HEq' | inversion LIn' ].
        }
        {
            case_eq (length eqns_hd =? pos); trivial.
            rewrite Nat.eqb_eq; move=> H; destruct H.
            move: used.
            unfold partial_used_in; unfold used_in; clear.
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            move=> [vL [e [ind [HEq [is_spec HIn]]]]].
            exists ind; split; trivial.
            exists expr; split; auto.
            move: HIn; inversion HEq; trivial.
        }
    }
    {
        simpl; trivial.
    }
    {
        simpl.
        move=> tree HRec_hd trees HRec_tl path pos [valid_hd valid_tl]; split; auto.
    }
Qed.

Lemma partial_valid_use_tree_0:
    forall v eqns tree path,
        partial_valid_use_tree 0 v tree path eqns ->
            valid_use_tree v tree path eqns.
Proof.
    move=> v eqns.
    refine (use_tree_find _ (fun trees => forall pos path,
        partial_valid_list_use_tree 0 v trees pos path eqns ->
            valid_list_use_tree v trees pos path eqns) _ _ _ _).
    {
        move=> uses t path; simpl.
        move=> HImp pos.
        specialize HImp with pos nil; rewrite cats0 in HImp.
        split; move=> H.
        by destruct HImp as [[] _].
        by destruct HImp as [_ []].
    }
    {
        move=> uses trees HRec; simpl; move=> path [used pvalid].
        split; auto.
        move=> pos; rewrite used.
        split; auto.
        move=> []; auto.
    }
    {
        simpl; trivial.
    }
    {
        simpl; move=> hd HRec_hd tl HRec_tl pos path [pvalid_hd pvalid_tl]; auto.
    }
Qed.

Lemma update_expr_soundness:
    forall (tctxt : list (ident * typ)) full_expr expr eqns_hd eqns_tl vars eL dependancies dependancies',
        update_expr expr (length eqns_hd) dependancies = Some dependancies' ->
        is_subexpr expr full_expr ->
        distinct (map fst tctxt) ->
        map fst tctxt = map fst dependancies ->
        list_rel use_tree_of_type (map snd dependancies) (map snd tctxt) ->
        Forall (fun p : ident * use_tree => let (v, t) := p in
            partial_valid_use_tree' (length eqns_hd) eL v t nil (eqns_hd ++ (vars, full_expr) :: eqns_tl)) dependancies ->
        (forall v, In var (expr_freefullvars expr) v -> valid_var_utree dependancies' v) /\
        list_rel use_tree_of_type (map snd dependancies') (map snd tctxt) /\
        map fst tctxt = map fst dependancies' /\
        list_rel sub_utree (map snd dependancies) (map snd dependancies') /\
        Forall (fun p : ident * use_tree => let (v, t) := p in
            partial_valid_use_tree' (length eqns_hd) (expr :: eL) v t nil (eqns_hd ++ (vars, full_expr) :: eqns_tl)) dependancies'.
Proof.
    move=> tctxt full_expr expr eqns_hd eqns_tl vars; move: expr.
    refine (expr_find _ (fun el => forall expr_ctxt dependancies dependancies',
        update_list_expr el (length eqns_hd) dependancies = Some dependancies' ->
        Forall (fun e => is_subexpr e full_expr) (list_of_expr_list el) ->
        distinct (map fst tctxt) ->
        map fst tctxt = map fst dependancies ->
        list_rel use_tree_of_type (map snd dependancies) (map snd tctxt) ->
        Forall (fun p : ident * use_tree => let (v, t) := p in
            partial_valid_use_tree' (length eqns_hd) expr_ctxt v t nil (eqns_hd ++ (vars, full_expr) :: eqns_tl)) dependancies ->
        map fst tctxt = map fst dependancies' /\
        list_rel use_tree_of_type (map snd dependancies') (map snd tctxt) /\
        Forall (fun e => forall v, In var (expr_freefullvars e) v -> valid_var_utree dependancies' v) (list_of_expr_list el) /\
        list_rel sub_utree (map snd dependancies) (map snd dependancies') /\
        Forall (fun p : ident * use_tree => let (v, t) := p in
            partial_valid_use_tree' (length eqns_hd) (list_of_expr_list el ++ expr_ctxt) v t nil (eqns_hd ++ (vars, full_expr) :: eqns_tl)) dependancies'
        ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: simpl.
    {
        move=> z o eL dependancies dependancies' H; inversion H; auto.
        move=> _ _ fst_eq type_soundness Hvalid.
        split; [> by move=> v HIn; inversion HIn | idtac ].
        split; trivial.
        split; trivial.
        split.
        {
            clear; induction map; constructor; auto.
            exact (sub_utree_refl _).
        }
        rewrite Forall_forall; rewrite Forall_forall in Hvalid.
        move=> [v t] HIn.
        rewrite <-(partial_valid_use_tree'_change_list eL).
        by exact (Hvalid _ HIn).
        clear.
        move=> v'; split; move=> [e [LIn EIn]]; exists e; split; trivial.
        by constructor.
        inversion LIn as [HEq|]; trivial.
        destruct HEq; simpl in EIn.
        inversion EIn.
    }
    (* ExpVar *)
    {
        move=> [v|[v|] ind] eL dependancies dependancies'.
        3: by idtac.
        all: move=> update_eq HIn_imp Hdistinct fst_eq_in type_soundness Hvalid.
        all: rewrite fst_eq_in in Hdistinct.
        all: destruct (update_ctxt_soundness _ _ _ Hdistinct _ update_eq) as [Hdistinct' [is_map' [fst_eq changed_info]]].
        all: split.
        all: swap 2 3.
        1,2: move=> v' HIn; inversion HIn as [H']; destruct H'; clear HIn; simpl.
        1,2: move: changed_info Hdistinct'; clear.
        1,2: move=> H; induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
        1,3: move=> H; destruct (H Logic.eq_refl).
        1,2: destruct H_hd as [-> H_hd]; rewrite ident_beq_sym; destruct ident_beq.
        by discriminate.
        by assumption.
        by move=> _; refine (update_use_tree_access _ _ _ _ H_hd).
        by assumption.
        all: split.
        all: swap 2 3.
        1,2: move: changed_info type_soundness; clear.
        1,2: pose (tctxt' := map snd tctxt); fold tctxt'.
        1,2: move=> H; move: tctxt'; clear tctxt.
        1,2: induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
        1-4: move=> tctxt H; inversion H; constructor; auto.
        1,2: destruct H_hd as [-> H_hd]; destruct ident_beq.
        2,4: destruct H_hd; assumption.
        1,2: refine (update_use_tree_type_soundness _ _ _ _ _ H_hd _); assumption.
        all: split; [ by rewrite <- fst_eq; assumption | idtac ].
        all: split.
        all: swap 2 3.
        1,2: move: changed_info; clear.
        1,2: move=> H; induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
        1-4: constructor; destruct H_hd as [-> H_hd].
        2,4: by assumption.
        1,2: destruct ident_beq.
        2,4: by destruct H_hd; exact (sub_utree_refl _).
        1,2: by exact (update_use_tree_subtree _ _ _ _ H_hd).
        {
            move: changed_info Hvalid; clear.
            move=> H; induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
            all: move=> H; inversion H as [|p1' t1' p_hd p_tl]; clear H; constructor; auto.
            destruct H_hd as [-> H_hd].
            case_eq (ident_beq k2 v); move=> HEq; rewrite HEq in H_hd.
            {
                rewrite ident_beq_eq in HEq; destruct HEq.
                move: H_hd p_hd; clear.
                destruct v1 as [uses tree|uses trees]; simpl.
                all: move=> H; inversion H as [H']; clear H H' v2; simpl.
                {
                    move=> H pos l'; specialize H with pos l'; split.
                    {
                        move=> [[HEq|LIn] Empty].
                        {
                            destruct HEq; split; trivial.
                            rewrite Nat.eqb_refl.
                            unfold partial_used_in; rewrite Empty.
                            eexists; split; [> by constructor | eexists ].
                            simpl; split; [> left; reflexivity | right; simpl ].
                            split; [> constructor | reflexivity ].
                        }
                        {
                            destruct H as [[H1 H2] _]; split; trivial.
                            destruct (_ =? _); trivial; rewrite Empty; clear.
                            unfold partial_used_in.
                            eexists; split; [> by constructor | eexists ].
                            simpl; split; [> left; reflexivity | right; simpl ].
                            split; [> constructor | reflexivity ].
                        }
                    }
                    {
                        move=> [HInf Hdef].
                        case_eq (length eqns_hd =? pos); move=> HEq; rewrite HEq in Hdef.
                        all: rewrite HEq in H.
                        {
                            rewrite Nat.eqb_eq in HEq; split; auto.
                            unfold partial_used_in in Hdef; simpl in Hdef.
                            destruct Hdef as [ind [is_spec [e' [[<-|LIn] HIn]]]].
                            {
                                destruct HIn as [Abs|[_ ->]]; [> inversion Abs | inversion is_spec; reflexivity ].
                            }
                            {
                                destruct H as [_ []]; trivial.
                                split; trivial.
                                unfold partial_used_in.
                                eexists; split; [> exact is_spec | eexists ].
                                split; [> exact LIn | exact HIn ].
                            }
                        }
                        {
                            destruct H as [_ []]; split; auto.
                        }
                    }
                }
                {
                    move=> [H H']; split.
                    {
                        clear H'; move=> pos; specialize H with pos.
                        rewrite H; clear H; split.
                        {
                            move=> [HEq|[HInf pused]].
                            {
                                destruct HEq; split; trivial.
                                rewrite Nat.eqb_refl.
                                unfold partial_used_in.
                                eexists; split; [> by constructor | eexists ].
                                simpl; split; [> left; reflexivity | right; simpl ].
                                split; [> constructor | reflexivity ].
                            }
                            {
                                split; trivial.
                                destruct (_ =? _); trivial; clear.
                                unfold partial_used_in.
                                eexists; split; [> by constructor | eexists ].
                                simpl; split; [> left; reflexivity | right; simpl ].
                                split; [> constructor | reflexivity ].
                            }
                        }
                        {
                            move=> [HInf Hdef].
                            case_eq (length eqns_hd =? pos); move=> HEq; rewrite HEq in Hdef.
                            {
                                rewrite Nat.eqb_eq in HEq; auto.
                            }
                            {
                                right; auto.
                            }
                        }
                    }
                    {
                        move: H'; clear.
                        pose (p := 0); fold p; move: p.
                        induction trees; simpl; trivial.
                        move=> pos [valid_hd valid_tl]; split; auto.
                        apply partial_valid_use_tree_Var; auto.
                    }
                }
            }
            {
                destruct H_hd.
                apply partial_valid_use_tree_change_name; trivial.
                simpl; rewrite <-ident_beq_eq; rewrite ident_beq_sym.
                rewrite not_true_iff_false; assumption.
            }
        }
        {
            move: HIn_imp changed_info Hvalid; clear.
            move=> is_sub H; induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
            all: move=> H; inversion H as [|p1' t1' p_hd p_tl]; clear H; constructor; auto.
            destruct H_hd as [-> H_hd].
            case_eq (ident_beq k2 v); move=> HEq; rewrite HEq in H_hd.
            {
                rewrite ident_beq_eq in HEq; destruct HEq.
                move: is_sub H_hd p_hd; clear.
                move=> is_sub update_eq p_valid.
                refine (update_use_tree_soundness _ _ _ _ _ _ _ _ _ nil _ update_eq _ _ _); trivial.
                constructor.
            }
            {
                destruct H_hd.
                apply partial_valid_use_tree_change_name; trivial.
                simpl; rewrite <-ident_beq_eq; rewrite ident_beq_sym.
                rewrite not_true_iff_false; assumption.
            }
        }
    }
    (* Tuple *)
    {
        simpl.
        move=> eL HRec ctxt dependancies dependancies' HEq is_sub is_map fst_eq type_soundness HValid.
        apply (HRec ctxt) in HEq; trivial.
        {
            destruct HEq as [Eq [type_soundness' [acc_valid [all_sub valid]]]].
            split.
            {
                move: acc_valid; clear.
                induction eL; simpl.
                by move=> _ v HIn; inversion HIn.
                move=> acc_valid; inversion acc_valid.
                move=> v HIn; inversion HIn; auto.
            }
            split; [> assumption | split; trivial].
            split; trivial.
            move: valid; clear; move=> valid.
            rewrite Forall_forall; rewrite Forall_forall in valid.
            move=> [v t] LIn; apply valid in LIn.
            rewrite <-(partial_valid_use_tree'_change_list (list_of_expr_list eL ++ ctxt)); trivial.
            clear.
            move=> v; split; move=> [e [LIn HIn]].
            {
                rewrite List.in_app_iff in LIn.
                destruct LIn as [LIn|LIn].
                {
                    eexists; split; simpl.
                    by left; reflexivity.
                    simpl.
                    induction eL as [|hd tl HRec]; simpl in *.
                    by idtac.
                    destruct LIn as [HEq|LIn].
                    by destruct HEq; constructor.
                    by apply HRec in LIn; constructor.
                }
                {
                    exists e; split; auto.
                    by constructor.
                }
            }
            {
                inversion LIn as [HEq|LIn']; clear LIn.
                {
                    destruct HEq; simpl in *.
                    induction eL as [|hd tl HRec]; simpl in *.
                    by inversion HIn.
                    inversion HIn as [|x H].
                    by exists hd; auto.
                    destruct (HRec H) as [e [LIn EIn]].
                    exists e; auto.
                }
                {
                    exists e; split; auto.
                    rewrite List.in_app_iff; auto.
                }
            }
        }
        {
            move: is_sub; clear.
            assert (forall eL_hd, (Forall (fun e => (exists e', List.In e' eL_hd /\ is_subexpr e e') \/ is_subexpr_l e eL)) (eL_hd ++ list_of_expr_list eL)).
            {
                induction eL as [|hd tl HRec]; simpl.
                {
                    move=> eL_hd; rewrite cats0.
                    rewrite Forall_forall.
                    move=> e HIn; left.
                    exists e; split; trivial.
                    apply is_subexpr_refl.
                }
                {
                    move=> eL_hd.
                    specialize HRec with (eL_hd ++ [:: hd]).
                    rewrite <-app_assoc in HRec; simpl in HRec.
                    rewrite Forall_forall in HRec; rewrite Forall_forall.
                    move=> e; specialize HRec with e.
                    rewrite List.in_app_iff; rewrite List.in_app_iff in HRec.
                    move=> [H|H].
                    {
                        destruct HRec as [H1|]; auto.
                        destruct H1 as [e' [LIn is_sub]].
                        rewrite List.in_app_iff in LIn.
                        destruct LIn as [H'|H'].
                        {
                            left; exists e'; auto.
                        }
                        {
                            inversion H' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                            auto.
                        }
                    }
                    {
                        inversion H as [HEq|HIn].
                        {
                            destruct HEq; right; left; apply is_subexpr_refl.
                        }
                        {
                            destruct HRec as [[e' [HIn' is_sub]]|]; auto.
                            rewrite List.in_app_iff in HIn'.
                            destruct HIn' as [HIn'|HIn'].
                            {
                                left; exists e'; auto.
                            }
                            {
                                inversion HIn' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                                auto.
                            }
                        }
                    }
                }
            }
            specialize H with nil.
            rewrite Forall_forall; rewrite Forall_forall in H.
            move=> is_sub e HIn; specialize H with e.
            simpl in H; apply H in HIn; clear H.
            destruct HIn as [[e' [[] H]]|is_sub'].
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; assumption.
        }
    }
    (* BuildArray *)
    {
        simpl.
        move=> eL HRec ctxt dependancies dependancies' HEq is_sub is_map fst_eq type_soundness HValid.
        apply (HRec ctxt) in HEq; trivial.
        {
            destruct HEq as [Eq [type_soundness' [acc_valid [all_sub valid]]]].
            split.
            {
                move: acc_valid; clear.
                induction eL; simpl.
                by move=> _ v HIn; inversion HIn.
                move=> acc_valid; inversion acc_valid.
                move=> v HIn; inversion HIn; auto.
            }
            split; [> assumption | split; trivial].
            split; trivial.
            move: valid; clear; move=> valid.
            rewrite Forall_forall; rewrite Forall_forall in valid.
            move=> [v t] LIn; apply valid in LIn.
            rewrite <-(partial_valid_use_tree'_change_list (list_of_expr_list eL ++ ctxt)); trivial.
            clear.
            move=> v; split; move=> [e [LIn HIn]].
            {
                rewrite List.in_app_iff in LIn.
                destruct LIn as [LIn|LIn].
                {
                    eexists; split; simpl.
                    by left; reflexivity.
                    simpl.
                    induction eL as [|hd tl HRec]; simpl in *.
                    by idtac.
                    destruct LIn as [HEq|LIn].
                    by destruct HEq; constructor.
                    by apply HRec in LIn; constructor.
                }
                {
                    exists e; split; auto.
                    by constructor.
                }
            }
            {
                inversion LIn as [HEq|LIn']; clear LIn.
                {
                    destruct HEq; simpl in *.
                    induction eL as [|hd tl HRec]; simpl in *.
                    by inversion HIn.
                    inversion HIn as [|x H].
                    by exists hd; auto.
                    destruct (HRec H) as [e [LIn EIn]].
                    exists e; auto.
                }
                {
                    exists e; split; auto.
                    rewrite List.in_app_iff; auto.
                }
            }
        }
        {
            move: is_sub; clear.
            assert (forall eL_hd, (Forall (fun e => (exists e', List.In e' eL_hd /\ is_subexpr e e') \/ is_subexpr_l e eL)) (eL_hd ++ list_of_expr_list eL)).
            {
                induction eL as [|hd tl HRec]; simpl.
                {
                    move=> eL_hd; rewrite cats0.
                    rewrite Forall_forall.
                    move=> e HIn; left.
                    exists e; split; trivial.
                    apply is_subexpr_refl.
                }
                {
                    move=> eL_hd.
                    specialize HRec with (eL_hd ++ [:: hd]).
                    rewrite <-app_assoc in HRec; simpl in HRec.
                    rewrite Forall_forall in HRec; rewrite Forall_forall.
                    move=> e; specialize HRec with e.
                    rewrite List.in_app_iff; rewrite List.in_app_iff in HRec.
                    move=> [H|H].
                    {
                        destruct HRec as [H1|]; auto.
                        destruct H1 as [e' [LIn is_sub]].
                        rewrite List.in_app_iff in LIn.
                        destruct LIn as [H'|H'].
                        {
                            left; exists e'; auto.
                        }
                        {
                            inversion H' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                            auto.
                        }
                    }
                    {
                        inversion H as [HEq|HIn].
                        {
                            destruct HEq; right; left; apply is_subexpr_refl.
                        }
                        {
                            destruct HRec as [[e' [HIn' is_sub]]|]; auto.
                            rewrite List.in_app_iff in HIn'.
                            destruct HIn' as [HIn'|HIn'].
                            {
                                left; exists e'; auto.
                            }
                            {
                                inversion HIn' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                                auto.
                            }
                        }
                    }
                }
            }
            specialize H with nil.
            rewrite Forall_forall; rewrite Forall_forall in H.
            move=> is_sub e HIn; specialize H with e.
            simpl in H; apply H in HIn; clear H.
            destruct HIn as [[e' [[] H]]|is_sub'].
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; assumption.
        }
    }
    (* Not *)
    {
        simpl.
        move=> e HRec ctxt dependancies dependancies' HEq is_sub is_map fst_eq type_soundness HValid.
        apply (HRec ctxt) in HEq; trivial.
        {
            destruct HEq as [Eq [type_soundness' [acc_valid [all_sub valid]]]].
            do 4 (split; trivial).
            rewrite Forall_forall; rewrite Forall_forall in valid.
            move=> [v t] LIn; apply valid in LIn.
            rewrite <-(partial_valid_use_tree'_change_list (e::ctxt)); trivial.
            clear.
            move=> v; split; move=> [e' [LIn HIn]]; inversion LIn as [HEq|LIn'].
            {
                exists (Not e); destruct HEq.
                split; simpl; auto.
            }
            {
                exists e'; simpl; auto.
            }
            {
                destruct HEq.
                exists e; split; simpl in *; auto.
            }
            {
                exists e'; simpl; auto.
            }
        }
        {
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; apply is_subexpr_refl.
        }
    }
    (* Log *)
    {
        move=> lop e1 HRec1 e2 HRec2 ctxt dependancies dependancies'.
        move: (HRec1 ctxt dependancies); clear HRec1; move=> HRec1.
        destruct (update_expr e1) as [dep1|]; [> idtac | by idtac ].
        move=> update_eq2 imp_In Hdistinct fst_eq type_soundness imp_valid.
        move: (HRec1 dep1); clear HRec1.
        impl_tac; trivial.
        impl_tac.
        {
            refine (is_subexpr_trans _ _ _ _ imp_In); simpl.
            right; left; apply is_subexpr_refl.
        }
        do 4 (impl_tac; trivial).
        move=> [valid_access1 [type_soundness1 [fst_eq1 [subs1 Hvalid]]]].
        apply (HRec2 (e1 :: ctxt)) in update_eq2; clear HRec2.
        {
            destruct update_eq2 as [valid_access2 [type_soundness1' [HEq1 [subs2 imp_valid']]]].
            split.
            {
                move=> v HIn; inversion HIn as [elt HIn'|elt HIn']; auto.
                apply valid_access1 in HIn'.
                move: (Logic.eq_sym fst_eq1) subs2 HIn'; rewrite HEq1; clear.
                apply valid_var_utree_keep.
            }
            split; [> assumption | idtac ].
            split; [> assumption | idtac ].
            split.
            by exact (list_rel_trans sub_utree_trans _ _ _ subs1 subs2).
            rewrite Forall_forall in imp_valid'; rewrite Forall_forall.
            move=> [v t] HIn; apply imp_valid' in HIn.
            rewrite <-(partial_valid_use_tree'_change_list (e2 :: e1 :: ctxt)); auto.
            split; move=> [e [LIn EIn]]; inversion LIn as [HEq|LIn'].
            {
                eexists; split; simpl.
                by left.
                simpl; destruct HEq.
                by constructor.
            }
            {
                inversion LIn' as [HEq|LIn'']; eexists; split; simpl.
                by left.
                by simpl; destruct HEq; constructor.
                by right; exact LIn''.
                by assumption.
            }
            {
                destruct HEq; simpl in EIn.
                inversion EIn as [elt EIn'|elt EIn']; [> exists e1 | exists e2].
                all: split; simpl; auto.
            }
            {
                exists e; split; simpl; auto.
            }
        }
        {
            refine (is_subexpr_trans _ _ _ _ imp_In); simpl.
            right; right; apply is_subexpr_refl.
        }
        1,3,4: by assumption.
        rewrite <-fst_eq1; auto.
    }
    (* Arith *)
    {
        move=> aop e1 HRec1 e2 HRec2 ctxt dependancies dependancies'.
        move: (HRec1 ctxt dependancies); clear HRec1; move=> HRec1.
        destruct (update_expr e1) as [dep1|]; [> idtac | by idtac ].
        move=> update_eq2 imp_In Hdistinct fst_eq type_soundness imp_valid.
        move: (HRec1 dep1); clear HRec1.
        impl_tac; trivial.
        impl_tac.
        {
            refine (is_subexpr_trans _ _ _ _ imp_In); simpl.
            right; left; apply is_subexpr_refl.
        }
        do 4 (impl_tac; trivial).
        move=> [valid_access1 [type_soundness1 [fst_eq1 [subs1 Hvalid]]]].
        apply (HRec2 (e1 :: ctxt)) in update_eq2; clear HRec2.
        {
            destruct update_eq2 as [valid_access2 [type_soundness1' [HEq1 [subs2 imp_valid']]]].
            split.
            {
                move=> v HIn; inversion HIn as [elt HIn'|elt HIn']; auto.
                apply valid_access1 in HIn'.
                move: (Logic.eq_sym fst_eq1) subs2 HIn'; rewrite HEq1; clear.
                apply valid_var_utree_keep.
            }
            split; [> assumption | idtac ].
            split; [> assumption | idtac ].
            split.
            by exact (list_rel_trans sub_utree_trans _ _ _ subs1 subs2).
            rewrite Forall_forall in imp_valid'; rewrite Forall_forall.
            move=> [v t] HIn; apply imp_valid' in HIn.
            rewrite <-(partial_valid_use_tree'_change_list (e2 :: e1 :: ctxt)); auto.
            split; move=> [e [LIn EIn]]; inversion LIn as [HEq|LIn'].
            {
                eexists; split; simpl.
                by left.
                simpl; destruct HEq.
                by constructor.
            }
            {
                inversion LIn' as [HEq|LIn'']; eexists; split; simpl.
                by left.
                by simpl; destruct HEq; constructor.
                by right; exact LIn''.
                by assumption.
            }
            {
                destruct HEq; simpl in EIn.
                inversion EIn as [elt EIn'|elt EIn']; [> exists e1 | exists e2].
                all: split; simpl; auto.
            }
            {
                exists e; split; simpl; auto.
            }
        }
        {
            refine (is_subexpr_trans _ _ _ _ imp_In); simpl.
            right; right; apply is_subexpr_refl.
        }
        1,3,4: by assumption.
        rewrite <-fst_eq1; auto.
    }
    (* Shift op *)
    {
        simpl.
        move=> sop e HRec ae ctxt dependancies dependancies' HEq is_sub is_map fst_eq type_soundness HValid.
        apply (HRec ctxt) in HEq; trivial.
        {
            destruct HEq as [Eq [type_soundness' [acc_valid [all_sub valid]]]].
            do 4 (split; trivial).
            rewrite Forall_forall; rewrite Forall_forall in valid.
            move=> [v t] LIn; apply valid in LIn.
            rewrite <-(partial_valid_use_tree'_change_list (e::ctxt)); trivial.
            clear.
            move=> v; split; move=> [e' [LIn HIn]]; inversion LIn as [HEq|LIn'].
            {
                eexists; simpl; split; [> left; reflexivity | idtac ].
                simpl; destruct HEq; assumption.
            }
            {
                exists e'; simpl; auto.
            }
            {
                destruct HEq.
                exists e; split; simpl in *; auto.
            }
            {
                exists e'; simpl; auto.
            }
        }
        {
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; apply is_subexpr_refl.
        }
    }
    (* Shuffle *)
    {
        move=> [v|[v|] ind] l eL dependancies dependancies'.
        3: by idtac.
        all: move=> update_eq HIn_imp Hdistinct fst_eq_in type_soundness Hvalid.
        all: rewrite fst_eq_in in Hdistinct.
        all: destruct (update_ctxt_soundness _ _ _ Hdistinct _ update_eq) as [Hdistinct' [is_map' [fst_eq changed_info]]].
        all: split.
        all: swap 2 3.
        1,2: move=> v' HIn; inversion HIn as [H']; destruct H'; clear HIn; simpl.
        1,2: move: changed_info Hdistinct'; clear.
        1,2: move=> H; induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
        1,3: move=> H; destruct (H Logic.eq_refl).
        1,2: destruct H_hd as [-> H_hd]; rewrite ident_beq_sym; destruct ident_beq.
        by discriminate.
        by assumption.
        by move=> _; refine (update_use_tree_access _ _ _ _ H_hd).
        by assumption.
        all: split.
        all: swap 2 3.
        1,2: move: changed_info type_soundness; clear.
        1,2: pose (tctxt' := map snd tctxt); fold tctxt'.
        1,2: move=> H; move: tctxt'; clear tctxt.
        1,2: induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
        1-4: move=> tctxt H; inversion H; constructor; auto.
        1,2: destruct H_hd as [-> H_hd]; destruct ident_beq.
        2,4: destruct H_hd; assumption.
        1,2: refine (update_use_tree_type_soundness _ _ _ _ _ H_hd _); assumption.
        all: split; [ by rewrite <- fst_eq; assumption | idtac ].
        all: split.
        all: swap 2 3.
        1,2: move: changed_info; clear.
        1,2: move=> H; induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
        1-4: constructor; destruct H_hd as [-> H_hd].
        2,4: by assumption.
        1,2: destruct ident_beq.
        2,4: by destruct H_hd; exact (sub_utree_refl _).
        1,2: by exact (update_use_tree_subtree _ _ _ _ H_hd).
        {
            move: changed_info Hvalid; clear.
            move=> H; induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
            all: move=> H; inversion H as [|p1' t1' p_hd p_tl]; clear H; constructor; auto.
            destruct H_hd as [-> H_hd].
            case_eq (ident_beq k2 v); move=> HEq; rewrite HEq in H_hd.
            {
                rewrite ident_beq_eq in HEq; destruct HEq.
                move: H_hd p_hd; clear.
                destruct v1 as [uses tree|uses trees]; simpl.
                all: move=> H; inversion H as [H']; clear H H' v2; simpl.
                {
                    move=> H pos l'; specialize H with pos l'; split.
                    {
                        move=> [[HEq|LIn] Empty].
                        {
                            destruct HEq; split; trivial.
                            rewrite Nat.eqb_refl.
                            unfold partial_used_in; rewrite Empty.
                            eexists; split; [> by constructor | eexists ].
                            simpl; split; [> left; reflexivity | right; simpl ].
                            split; [> constructor | reflexivity ].
                        }
                        {
                            destruct H as [[H1 H2] _]; split; trivial.
                            destruct (_ =? _); trivial; rewrite Empty; clear.
                            unfold partial_used_in.
                            eexists; split; [> by constructor | eexists ].
                            simpl; split; [> left; reflexivity | right; simpl ].
                            split; [> constructor | reflexivity ].
                        }
                    }
                    {
                        move=> [HInf Hdef].
                        case_eq (length eqns_hd =? pos); move=> HEq; rewrite HEq in Hdef.
                        all: rewrite HEq in H.
                        {
                            rewrite Nat.eqb_eq in HEq; split; auto.
                            unfold partial_used_in in Hdef; simpl in Hdef.
                            destruct Hdef as [ind [is_spec [e' [[<-|LIn] HIn]]]].
                            {
                                destruct HIn as [Abs|[_ ->]]; [> inversion Abs | inversion is_spec; reflexivity ].
                            }
                            {
                                destruct H as [_ []]; trivial.
                                split; trivial.
                                unfold partial_used_in.
                                eexists; split; [> exact is_spec | eexists ].
                                split; [> exact LIn | exact HIn ].
                            }
                        }
                        {
                            destruct H as [_ []]; split; auto.
                        }
                    }
                }
                {
                    move=> [H H']; split.
                    {
                        clear H'; move=> pos; specialize H with pos.
                        rewrite H; clear H; split.
                        {
                            move=> [HEq|[HInf pused]].
                            {
                                destruct HEq; split; trivial.
                                rewrite Nat.eqb_refl.
                                unfold partial_used_in.
                                eexists; split; [> by constructor | eexists ].
                                simpl; split; [> left; reflexivity | right; simpl ].
                                split; [> constructor | reflexivity ].
                            }
                            {
                                split; trivial.
                                destruct (_ =? _); trivial; clear.
                                unfold partial_used_in.
                                eexists; split; [> by constructor | eexists ].
                                simpl; split; [> left; reflexivity | right; simpl ].
                                split; [> constructor | reflexivity ].
                            }
                        }
                        {
                            move=> [HInf Hdef].
                            case_eq (length eqns_hd =? pos); move=> HEq; rewrite HEq in Hdef.
                            {
                                rewrite Nat.eqb_eq in HEq; auto.
                            }
                            {
                                right; auto.
                            }
                        }
                    }
                    {
                        move: H'; clear.
                        pose (p := 0); fold p; move: p.
                        induction trees; simpl; trivial.
                        move=> pos [valid_hd valid_tl]; split; auto.
                        rewrite <-(partial_valid_use_tree'_change_list (ExpVar (Var k2) :: eL)).
                        by apply partial_valid_use_tree_Var; auto.
                        {
                            clear; simpl; intro.
                            split; move=> [e [[<-|LIn] HIn]].
                            1,3: eexists; split; [ left; reflexivity | idtac ].
                            1,2: simpl in *; assumption.
                            all: eexists; split; [ right; exact LIn | exact HIn ].
                        }
                    }
                }
            }
            {
                destruct H_hd.
                rewrite <-(partial_valid_use_tree'_change_list (ExpVar (Var v) :: eL)).
                {
                    apply partial_valid_use_tree_change_name; trivial.
                    simpl; rewrite <-ident_beq_eq; rewrite ident_beq_sym.
                    rewrite not_true_iff_false; assumption.
                }
                {
                    clear; simpl; intro.
                    split; move=> [e [[<-|LIn] HIn]].
                    1,3: eexists; split; [ left; reflexivity | idtac ].
                    1,2: simpl in *; assumption.
                    all: eexists; split; [ right; exact LIn | exact HIn ].
                }
            }
        }
        {
            move: HIn_imp changed_info Hvalid; clear.
            move=> is_sub H; induction H as [|[k1 v1] [k2 v2] t1 t2 H_hd H_tl HRec]; simpl in *.
            all: move=> H; inversion H as [|p1' t1' p_hd p_tl]; clear H; constructor; auto.
            destruct H_hd as [-> H_hd].
            case_eq (ident_beq k2 v); move=> HEq; rewrite HEq in H_hd.
            {
                rewrite ident_beq_eq in HEq; destruct HEq.
                move: is_sub H_hd p_hd; clear.
                move=> is_sub update_eq p_valid.
                rewrite <-(partial_valid_use_tree'_change_list (ExpVar (Index (Var k2) ind) :: eL)).
                {
                    refine (update_use_tree_soundness _ _ _ _ _ _ _ _ _ nil _ update_eq _ _ _); trivial.
                    by constructor.
                    refine (is_subexpr_trans _ _ _ _ is_sub).
                    simpl; auto.
                }
                {
                    clear; simpl; intro.
                    split; move=> [e [[<-|LIn] HIn]].
                    1,3: eexists; split; [ left; reflexivity | idtac ].
                    1,2: simpl in *; assumption.
                    all: eexists; split; [ right; exact LIn | exact HIn ].
                }
            }
            {
                destruct H_hd.
                rewrite <-(partial_valid_use_tree'_change_list (ExpVar (Index (Var v) ind):: eL)).
                {
                    apply partial_valid_use_tree_change_name; trivial.
                    simpl; rewrite <-ident_beq_eq; rewrite ident_beq_sym.
                    rewrite not_true_iff_false; assumption.
                }
                {
                    clear; simpl; intro.
                    split; move=> [e [[<-|LIn] HIn]].
                    1,3: eexists; split; [ left; reflexivity | idtac ].
                    1,2: simpl in *; assumption.
                    all: eexists; split; [ right; exact LIn | exact HIn ].
                }
            }
        }
    }
    (* Bitmask *)
    {
        simpl.
        move=> e HRec ae ctxt dependancies dependancies' HEq is_sub is_map fst_eq type_soundness HValid.
        apply (HRec ctxt) in HEq; trivial.
        {
            destruct HEq as [Eq [type_soundness' [acc_valid [all_sub valid]]]].
            do 4 (split; trivial).
            rewrite Forall_forall; rewrite Forall_forall in valid.
            move=> [v t] LIn; apply valid in LIn.
            rewrite <-(partial_valid_use_tree'_change_list (e::ctxt)); trivial.
            clear.
            move=> v; split; move=> [e' [LIn HIn]]; inversion LIn as [HEq|LIn'].
            {
                eexists; simpl; split; [> left; reflexivity | idtac ].
                simpl; destruct HEq; assumption.
            }
            {
                exists e'; simpl; auto.
            }
            {
                destruct HEq.
                exists e; split; simpl in *; auto.
            }
            {
                exists e'; simpl; auto.
            }
        }
        {
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; apply is_subexpr_refl.
        }
    }
    (* Pack *)
    {
        move=> e1 HRec1 e2 HRec2 otyp ctxt dependancies dependancies'.
        move: (HRec1 ctxt dependancies); clear HRec1; move=> HRec1.
        destruct (update_expr e1) as [dep1|]; [> idtac | by idtac ].
        move=> update_eq2 imp_In Hdistinct fst_eq type_soundness imp_valid.
        move: (HRec1 dep1); clear HRec1.
        impl_tac; trivial.
        impl_tac.
        {
            refine (is_subexpr_trans _ _ _ _ imp_In); simpl.
            right; left; apply is_subexpr_refl.
        }
        do 4 (impl_tac; trivial).
        move=> [valid_access1 [type_soundness1 [fst_eq1 [subs1 Hvalid]]]].
        apply (HRec2 (e1 :: ctxt)) in update_eq2; clear HRec2.
        {
            destruct update_eq2 as [valid_access2 [type_soundness1' [HEq1 [subs2 imp_valid']]]].
            split.
            {
                move=> v HIn; inversion HIn as [elt HIn'|elt HIn']; auto.
                apply valid_access1 in HIn'.
                move: (Logic.eq_sym fst_eq1) subs2 HIn'; rewrite HEq1; clear.
                apply valid_var_utree_keep.
            }
            split; [> assumption | idtac ].
            split; [> assumption | idtac ].
            split.
            by exact (list_rel_trans sub_utree_trans _ _ _ subs1 subs2).
            rewrite Forall_forall in imp_valid'; rewrite Forall_forall.
            move=> [v t] HIn; apply imp_valid' in HIn.
            rewrite <-(partial_valid_use_tree'_change_list (e2 :: e1 :: ctxt)); auto.
            split; move=> [e [LIn EIn]]; inversion LIn as [HEq|LIn'].
            {
                eexists; split; simpl.
                by left.
                simpl; destruct HEq.
                by constructor.
            }
            {
                inversion LIn' as [HEq|LIn'']; eexists; split; simpl.
                by left.
                by simpl; destruct HEq; constructor.
                by right; exact LIn''.
                by assumption.
            }
            {
                destruct HEq; simpl in EIn.
                inversion EIn as [elt EIn'|elt EIn']; [> exists e1 | exists e2].
                all: split; simpl; auto.
            }
            {
                exists e; split; simpl; auto.
            }
        }
        {
            refine (is_subexpr_trans _ _ _ _ imp_In); simpl.
            right; right; apply is_subexpr_refl.
        }
        1,3,4: by assumption.
        rewrite <-fst_eq1; auto.
    }
    (* Fun *)
    {
        simpl.
        move=> i eL HRec ctxt dependancies dependancies' HEq is_sub is_map fst_eq type_soundness HValid.
        apply (HRec ctxt) in HEq; trivial.
        {
            destruct HEq as [Eq [type_soundness' [acc_valid [all_sub valid]]]].
            split.
            {
                move: acc_valid; clear.
                induction eL; simpl.
                by move=> _ v HIn; inversion HIn.
                move=> acc_valid; inversion acc_valid.
                move=> v HIn; inversion HIn; auto.
            }
            split; [> assumption | split; trivial].
            split; trivial.
            move: valid; clear; move=> valid.
            rewrite Forall_forall; rewrite Forall_forall in valid.
            move=> [v t] LIn; apply valid in LIn.
            rewrite <-(partial_valid_use_tree'_change_list (list_of_expr_list eL ++ ctxt)); trivial.
            clear.
            move=> v; split; move=> [e [LIn HIn]].
            {
                rewrite List.in_app_iff in LIn.
                destruct LIn as [LIn|LIn].
                {
                    eexists; split; simpl.
                    by left; reflexivity.
                    simpl.
                    induction eL as [|hd tl HRec]; simpl in *.
                    by idtac.
                    destruct LIn as [HEq|LIn].
                    by destruct HEq; constructor.
                    by apply HRec in LIn; constructor.
                }
                {
                    exists e; split; auto.
                    by constructor.
                }
            }
            {
                inversion LIn as [HEq|LIn']; clear LIn.
                {
                    destruct HEq; simpl in *.
                    induction eL as [|hd tl HRec]; simpl in *.
                    by inversion HIn.
                    inversion HIn as [|x H].
                    by exists hd; auto.
                    destruct (HRec H) as [e [LIn EIn]].
                    exists e; auto.
                }
                {
                    exists e; split; auto.
                    rewrite List.in_app_iff; auto.
                }
            }
        }
        {
            move: is_sub; clear.
            assert (forall eL_hd, (Forall (fun e => (exists e', List.In e' eL_hd /\ is_subexpr e e') \/ is_subexpr_l e eL)) (eL_hd ++ list_of_expr_list eL)).
            {
                induction eL as [|hd tl HRec]; simpl.
                {
                    move=> eL_hd; rewrite cats0.
                    rewrite Forall_forall.
                    move=> e HIn; left.
                    exists e; split; trivial.
                    apply is_subexpr_refl.
                }
                {
                    move=> eL_hd.
                    specialize HRec with (eL_hd ++ [:: hd]).
                    rewrite <-app_assoc in HRec; simpl in HRec.
                    rewrite Forall_forall in HRec; rewrite Forall_forall.
                    move=> e; specialize HRec with e.
                    rewrite List.in_app_iff; rewrite List.in_app_iff in HRec.
                    move=> [H|H].
                    {
                        destruct HRec as [H1|]; auto.
                        destruct H1 as [e' [LIn is_sub]].
                        rewrite List.in_app_iff in LIn.
                        destruct LIn as [H'|H'].
                        {
                            left; exists e'; auto.
                        }
                        {
                            inversion H' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                            auto.
                        }
                    }
                    {
                        inversion H as [HEq|HIn].
                        {
                            destruct HEq; right; left; apply is_subexpr_refl.
                        }
                        {
                            destruct HRec as [[e' [HIn' is_sub]]|]; auto.
                            rewrite List.in_app_iff in HIn'.
                            destruct HIn' as [HIn'|HIn'].
                            {
                                left; exists e'; auto.
                            }
                            {
                                inversion HIn' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                                auto.
                            }
                        }
                    }
                }
            }
            specialize H with nil.
            rewrite Forall_forall; rewrite Forall_forall in H.
            move=> is_sub e HIn; specialize H with e.
            simpl in H; apply H in HIn; clear H.
            destruct HIn as [[e' [[] H]]|is_sub'].
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; assumption.
        }
    }
    (* Fun_v *)
    {
        simpl.
        move=> i ae eL HRec ctxt dependancies dependancies' HEq is_sub is_map fst_eq type_soundness HValid.
        apply (HRec ctxt) in HEq; trivial.
        {
            destruct HEq as [Eq [type_soundness' [acc_valid [all_sub valid]]]].
            split.
            {
                move: acc_valid; clear.
                induction eL; simpl.
                by move=> _ v HIn; inversion HIn.
                move=> acc_valid; inversion acc_valid.
                move=> v HIn; inversion HIn; auto.
            }
            split; [> assumption | split; trivial].
            split; trivial.
            move: valid; clear; move=> valid.
            rewrite Forall_forall; rewrite Forall_forall in valid.
            move=> [v t] LIn; apply valid in LIn.
            rewrite <-(partial_valid_use_tree'_change_list (list_of_expr_list eL ++ ctxt)); trivial.
            clear.
            move=> v; split; move=> [e [LIn HIn]].
            {
                rewrite List.in_app_iff in LIn.
                destruct LIn as [LIn|LIn].
                {
                    eexists; split; simpl.
                    by left; reflexivity.
                    simpl.
                    induction eL as [|hd tl HRec]; simpl in *.
                    by idtac.
                    destruct LIn as [HEq|LIn].
                    by destruct HEq; constructor.
                    by apply HRec in LIn; constructor.
                }
                {
                    exists e; split; auto.
                    by constructor.
                }
            }
            {
                inversion LIn as [HEq|LIn']; clear LIn.
                {
                    destruct HEq; simpl in *.
                    induction eL as [|hd tl HRec]; simpl in *.
                    by inversion HIn.
                    inversion HIn as [|x H].
                    by exists hd; auto.
                    destruct (HRec H) as [e [LIn EIn]].
                    exists e; auto.
                }
                {
                    exists e; split; auto.
                    rewrite List.in_app_iff; auto.
                }
            }
        }
        {
            move: is_sub; clear.
            assert (forall eL_hd, (Forall (fun e => (exists e', List.In e' eL_hd /\ is_subexpr e e') \/ is_subexpr_l e eL)) (eL_hd ++ list_of_expr_list eL)).
            {
                induction eL as [|hd tl HRec]; simpl.
                {
                    move=> eL_hd; rewrite cats0.
                    rewrite Forall_forall.
                    move=> e HIn; left.
                    exists e; split; trivial.
                    apply is_subexpr_refl.
                }
                {
                    move=> eL_hd.
                    specialize HRec with (eL_hd ++ [:: hd]).
                    rewrite <-app_assoc in HRec; simpl in HRec.
                    rewrite Forall_forall in HRec; rewrite Forall_forall.
                    move=> e; specialize HRec with e.
                    rewrite List.in_app_iff; rewrite List.in_app_iff in HRec.
                    move=> [H|H].
                    {
                        destruct HRec as [H1|]; auto.
                        destruct H1 as [e' [LIn is_sub]].
                        rewrite List.in_app_iff in LIn.
                        destruct LIn as [H'|H'].
                        {
                            left; exists e'; auto.
                        }
                        {
                            inversion H' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                            auto.
                        }
                    }
                    {
                        inversion H as [HEq|HIn].
                        {
                            destruct HEq; right; left; apply is_subexpr_refl.
                        }
                        {
                            destruct HRec as [[e' [HIn' is_sub]]|]; auto.
                            rewrite List.in_app_iff in HIn'.
                            destruct HIn' as [HIn'|HIn'].
                            {
                                left; exists e'; auto.
                            }
                            {
                                inversion HIn' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                                auto.
                            }
                        }
                    }
                }
            }
            specialize H with nil.
            rewrite Forall_forall; rewrite Forall_forall in H.
            move=> is_sub e HIn; specialize H with e.
            simpl in H; apply H in HIn; clear H.
            destruct HIn as [[e' [[] H]]|is_sub'].
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; assumption.
        }
    }
    (* Enil *)
    {
        simpl.
        move=> ctxt dep1 dep2 H; inversion H as [H'].
        do 5 intro; repeat split; trivial.
        clear.
        induction dep2 as [|[k v] tl HRec]; simpl; constructor; trivial.
        exact (sub_utree_refl _).
    }
    (* Econs *)
    {
        simpl.
        move=> hd HRec_hd tl HRec_tl ctxt dependancies dependancies'.
        move: (HRec_hd ctxt dependancies); clear HRec_hd; move=> HRec_hd.
        destruct update_expr as [dep1|]; [> idtac | by idtac ].
        move=> update_tl_eq imp_In Hdistinct fst_eq type_soundness imp_valid.
        move: (HRec_hd dep1); clear HRec_hd.
        impl_tac; trivial.
        inversion imp_In as [|hd' tl' imp_In_hd imp_In_tl].
        do 5 (impl_tac; trivial).
        move=> [valid_acc1 [type_soundness' [fst_eq1 [subs1 imp_valid']]]].
        rewrite fst_eq1.
        move: (HRec_tl (hd :: ctxt) _ _ update_tl_eq); auto.
        do 5 (impl_tac; trivial).
        move=> [fst_eq' [type_soundness'' [valid_acc2 [subs2 imp_valid'']]]].
        split; [> rewrite <-fst_eq1; assumption | idtac ].
        split; trivial.
        split.
        {
            constructor; auto.
            move: valid_acc1 subs2 fst_eq'.
            rewrite fst_eq1; clear.
            move=> valid_acc subs fst_eq v LIn.
            exact (valid_var_utree_keep _ _ _ fst_eq subs (valid_acc _ LIn)).
        }
        split.
        by refine (list_rel_trans sub_utree_trans _ _ _ subs1 subs2).
        rewrite Forall_forall; rewrite Forall_forall in imp_valid''.
        move=> [v t] LIn.
        rewrite <-(partial_valid_use_tree'_change_list (list_of_expr_list tl ++ hd :: ctxt)).
        by refine (imp_valid'' _ LIn).
        clear.
        move=> v; split; move=> [e [LIn HIn]]; exists e; split; trivial.
        {
            rewrite List.in_app_iff in LIn.
            destruct LIn as [LIn'|LIn'].
            {
                constructor 2.
                rewrite List.in_app_iff; auto.
            }
            inversion LIn' as [HEq|LIn_tl].
            by destruct HEq; constructor.
            constructor 2.
            rewrite List.in_app_iff; auto.
        }
        {
            rewrite List.in_app_iff.
            inversion LIn as [HEq|LIn_tl].
            by right; constructor.
            rewrite List.in_app_iff in LIn_tl.
            destruct LIn_tl; auto.
            by right; constructor.
        }
    }
Qed.

Lemma valid_is_used_in:
    forall v eqns i path_in path_tl utree,
        valid_use_tree v utree path_in eqns ->
        utree_used utree path_tl i <->
            valid_utree_access' utree path_tl /\
            used_in v (path_in ++ path_tl) i eqns.
Proof.
    move=> v eqns i path_in path_tl; move: path_in.
    induction path_tl as [|path_hd path_tl HRec]; move=> path_in [uses_l typ|uses_l utrees]; simpl.
    {
        move=> H; rewrite H; rewrite cats0.
        split; move=> [_ H']; split; trivial.
    }
    {
        move=> [H _]; rewrite H; rewrite cats0.
        split.
        by split; trivial.
        by move=> [_ H']; assumption.
    }
    {
        move=> _; split; move=> [Abs _]; inversion Abs.
    }
    {
        move=> [_ valid].
        assert (forall pos,
            valid_list_use_tree v utrees pos path_in eqns ->
            utrees_used utrees path_tl path_hd i <->
            (path_hd < utrees_length utrees /\
                valid_utrees_access' utrees path_hd path_tl) /\
                used_in v (path_in ++ (path_hd + pos) :: path_tl) i eqns) as H.
        {
            move: HRec path_hd; clear.
            move=> HRec.
            induction utrees as [|utree utrees HRec_trees]; simpl.
            by intros; split; [> move=> [] | move=> [[_ []] _]].
            move=> [|path_hd] pos [valid_hd valid_tl].
            {
                rewrite (HRec _ _ valid_hd).
                rewrite add0n; rewrite <-app_assoc; simpl.
                split.
                by move=> [H1 H2]; auto.
                by move=> [[_ H1] H2]; auto.
            }
            {
                rewrite (HRec_trees _ _ valid_tl).
                rewrite addSn; rewrite addnS.
                split; move=> [[H H1] H2]; split; auto.
            }
        }
        specialize H with 0; rewrite addn0 in H.
        auto.
    }
Qed.

Lemma is_spec_preserve_utree_valid_access:
    forall path_nat path_in utree,
        list_rel is_specialization path_nat path_in ->
        valid_utree_access utree path_in ->
        valid_utree_access' utree path_nat.
Proof.
    move=> path_nat path_in utree lr; move: utree.
    induction lr as [|pnat_hd pin_hd pnat_tl pin_tl is_spec_hd is_spec_tl HRec].
    all: move=> [uses typ|uses utrees]; simpl.
    1-3: move=> H; exact H.
    inversion is_spec_hd as [ae i eval_eq|ae aeL i LIn eval_eq|ae1 ae2 i1 i2 i eval_eq1 eval_eq2 Ineq].
    {
        rewrite eval_eq.
        move=> [_ [tmp valid_acc]].
        inversion tmp as [|hd tl inf_length].
        split; [> assumption | idtac ].
        assert (forall pos pnat_hd,
            valid_utrees_access utrees pos [:: pnat_hd + pos] pin_tl ->
            pnat_hd < utrees_length utrees ->
            valid_utrees_access' utrees pnat_hd pnat_tl
        ) as imp_valid.
        2: by apply (imp_valid 0); [> rewrite addn0 | idtac ]; assumption.
        move: HRec; clear; move=> HRec.
        induction utrees as [|utree utrees HRec_trees]; simpl.
        by auto.
        move=> pos [|pnat_hd].
        {
            rewrite add0n; rewrite Nat.eqb_refl; simpl.
            move=> [_ H] _; apply HRec; assumption.
        }
        {
            move=> [H _] SInf; apply (HRec_trees pos.+1).
            by rewrite addnS; rewrite addSn in H; assumption.
            by auto.
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
        induction utrees as [|hd tl HRec_trees]; simpl; [> by auto | idtac ].
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
            rewrite addnS; rewrite <-addSn.
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
        induction utrees as [|hd tl HRec_trees]; simpl; [> by auto | idtac ].
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
            rewrite addSn; rewrite <-addnS.
            move=> SInf LIn [valid _].
            apply (HRec_trees pos.+1 pnat_hd); auto.
        }
    }
Qed.
