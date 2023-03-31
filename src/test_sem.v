From mathcomp Require Import all_ssreflect.
From Usuba Require Import usuba_AST usuba_sem equiv_rel.

Goal
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

Goal
    update (2::nil) (1::2::nil) (ASlice [:: 0] AAll) [:: CoIL 1] (DirH 8) = Some (1::2::nil, nil).
Proof.
    simpl; reflexivity.
Qed.

Goal
    forall arch prog type_ctxt ctxt opt_ctxt' var typ dir,
        find_val type_ctxt var = Some typ ->
        well_typed_ctxt type_ctxt ctxt ->
        convert_type typ nil = Some (dir, 2::nil) ->
        eval_deq arch prog type_ctxt ctxt
             (Eqn (Range (Var var) (Const_e 1) (Const_e 0)::nil) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                true) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = Some (CoIR dir (2::1::nil) (Some (2::nil))).
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
        destruct typ' as [|d m n|typ len]; simpl in Convert.
        by discriminate.
        all: swap 1 2.
        {
            destruct (eval_arith_expr nil len) as [ilen|].
            2: by discriminate.
            exfalso; move: Convert.
            clear.
            pose (p := [:: ilen]); fold p.
            assert (p <> nil) as NotEmpty by (unfold p; move=> Eq; discriminate).
            move: p NotEmpty; clear.
            induction typ as [|d m n|typ HRec len']; simpl.
            by discriminate.
            {
                destruct m.
                + move=> []; destruct d; auto.
                    3-6: by discriminate.
                    1-2: move=> a []; simpl; discriminate.
                + discriminate.
                + discriminate.
            }
            {
                destruct (eval_arith_expr nil len').
                2: by discriminate.
                move=> [|hd tl] NotEmpty.
                by exfalso; apply NotEmpty; reflexivity.
                apply HRec.
                discriminate.
            }
        }
        simpl in *.
        destruct m as [| |].
        2,3: by destruct valoType.
        destruct c as [|d' l form]; simpl.
        {
            destruct d.
            3-6: discriminate.
            all: inversion Convert.
            all: destruct valoType as [_ [_ HEq2]].
            all: symmetry in HEq2; destruct HEq2; discriminate.
        }
        destruct form.
        2: by destruct valoType.
        rewrite muln1 in valoType.
        destruct d.
        3-5: by discriminate.
        all: inversion Convert as [[HEq2 HEq3]]; clear Convert; simpl.
        all: destruct HEq2.
        all: symmetry in HEq3; destruct HEq3.
        all: destruct valoType as [simpl_eq [length_eq dir_eq]].
        all: rewrite length_eq; simpl.
        all: destruct l as [|h1 l].
        1,3: by discriminate.
        all: destruct l as [|h2 l].
        1,3: by discriminate.
        all: destruct l as [|].
        2,4: by discriminate.
        all: simpl.
        all: move=> <-; simpl.
        all: rewrite String.eqb_refl.
        all: reflexivity.
    }
    {
        simpl.
        move=> _ <-; simpl.
        rewrite String.eqb_refl.
        reflexivity.
    }
Qed.
