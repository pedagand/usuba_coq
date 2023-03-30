From mathcomp Require Import all_ssreflect.
From Usuba Require Import usuba_AST usuba_sem equiv_rel.

Lemma eval_asign:
    forall arch prog type_ctxt ctxt opt_ctxt' var typ dir,
        find_val type_ctxt var = Some typ ->
        well_typed_ctxt type_ctxt ctxt ->
        convert_type typ nil = Some (dir, 1::nil) ->
        eval_deq arch prog type_ctxt ctxt
            (Eqn (Index (Var var) (Const_e 0) :: (Index (Var var) (Const_e 0)) :: nil) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                true) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = Some (CoIR dir (2::nil) (Some (1::nil))).
Proof.
    simpl.
    unfold bind; unfold bind_aux_list.
    unfold bind_aux.
    simpl.
    move=> _ _ type_ctxt ctxt opt_ctxt var typ dir HEqType well_typed.
    rewrite HEqType; move=> Convert; rewrite Convert; simpl.
    case_eq (find_val ctxt var).
    {
        move=> c HEq.
        pose (p := well_typed_ctxt_imp_find_val _ _ _ _ well_typed HEq).
        destruct p as [typ' [find_typ valoType]].
        rewrite find_typ in HEqType; inversion HEqType as [HEq'].
        destruct HEq'; clear HEqType.
        destruct c as [|d [|hd tl] form]; simpl.
        {
            rewrite String.eqb_refl; simpl.
            move=> <-; simpl.
            rewrite String.eqb_refl; reflexivity.
        }
        {
            exfalso.
            apply (val_of_type_len _ _ _ dir _ [:: 1]) in valoType; trivial.
            simpl in valoType.
            unfold muln, muln_rec in valoType.
            rewrite PeanoNat.Nat.mul_1_l in valoType; discriminate.
        }
        destruct tl; simpl.
        {
            rewrite String.eqb_refl; simpl.
            move=> <-; simpl.
            rewrite String.eqb_refl; reflexivity.
        }
        {
            exfalso.
            apply (val_of_type_len _ _ _ dir _ [:: 1]) in valoType; trivial.
            simpl in valoType.
            unfold muln, muln_rec in valoType.
            rewrite PeanoNat.Nat.mul_1_l in valoType; discriminate.
        }
    }
    {
        move=> _; simpl; rewrite String.eqb_refl; simpl.
        move=> <-; simpl.
        rewrite String.eqb_refl; reflexivity.
    }
Qed.
