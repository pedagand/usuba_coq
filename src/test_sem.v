From mathcomp Require Import all_ssreflect.
From Usuba Require Import usuba_AST usuba_ASTProp usuba_sem equiv_rel.

Goal
    forall arch prog type_ctxt ctxt opt_ctxt' var typ dir,
        find_val type_ctxt var = Some typ ->
        well_typed_ctxt type_ctxt ctxt ->
        convert_type typ nil = Some (dir, 1::nil) ->
        find_val ctxt var = None ->
        eval_deq arch prog type_ctxt ctxt
            (Eqn (Index (Var var) (Const_e 0) :: (Index (Var var) (Const_e 0)) :: nil) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                false) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = None.
Proof.
    simpl.
    unfold bind; unfold bind_aux_list.
    unfold bind_aux.
    simpl.
    move=> _ _ type_ctxt ctxt opt_ctxt var typ dir HEqType well_typed.
    rewrite HEqType; move=> Convert; rewrite Convert; simpl.
    case_eq (find_val ctxt var).
    { by discriminate. }
    {
        move=> _ _; simpl.
        rewrite ident_beq_refl; simpl.
        move=> <-; simpl; reflexivity.
    }
Qed.

Goal
    forall arch prog type_ctxt ctxt opt_ctxt' var typ dir,
        find_val type_ctxt var = Some typ ->
        well_typed_ctxt type_ctxt ctxt ->
        convert_type typ nil = Some (dir, 1::nil) ->
        (exists v, eval_var (Index (Var var) (Const_e 0)) ctxt AAll = Some v) ->
        eval_deq arch prog type_ctxt ctxt
            (Eqn (Index (Var var) (Const_e 0) :: (Index (Var var) (Const_e 0)) :: nil) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                true) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = Some (CoIR dir (Some 2::nil) (Some (1::nil))).
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
            rewrite ident_beq_refl; simpl.
            move=> _ <-; simpl.
            rewrite ident_beq_refl; reflexivity.
        }
        all: apply (val_of_type_len _ _ _ dir _ [:: 1]) in valoType; trivial.
        {
            exfalso.
            simpl in valoType.
            unfold muln, muln_rec in valoType.
            destruct valoType as [_ Abs].
            rewrite PeanoNat.Nat.mul_1_l in Abs; discriminate.
        }
        destruct valoType as [FormEq length_eq].
        destruct form as [form|].
        2: by destruct FormEq.
        symmetry in FormEq; destruct FormEq; simpl.
        simpl in length_eq.
        rewrite mul1n in length_eq.
        inversion length_eq as [LengthEq]; clear length_eq.
        destruct tl; simpl.
        2: by discriminate.
        destruct hd as [hd|].
        2: by move=> []; discriminate.
        simpl; rewrite ident_beq_refl; simpl.
        move=> _ <-; simpl.
        rewrite ident_beq_refl; reflexivity.
    }
    {
        move=> _ []; discriminate.
    }
Qed.

Goal
    update (2::nil) (Some 1::Some 2::nil) (ASlice [:: 0] AAll) [:: CoIL 1] (DirH 8) true = Some (Some 1::Some 2::nil, nil).
Proof.
    simpl; reflexivity.
Qed.

Goal
    forall arch prog type_ctxt ctxt opt_ctxt' var typ dir,
        find_val type_ctxt var = Some typ ->
        well_typed_ctxt type_ctxt ctxt ->
        convert_type typ nil = Some (dir, 2::nil) ->
        find_val ctxt var = None ->
        eval_deq arch prog type_ctxt ctxt
             (Eqn (Range (Var var) (Const_e 1) (Const_e 0)::nil) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                false) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = Some (CoIR dir (Some 2::Some 1::nil) (Some (2::nil))).
Proof.
    simpl.
    unfold bind; unfold bind_aux_list.
    unfold bind_aux.
    simpl.
    move=> _ _ type_ctxt ctxt opt_ctxt var typ dir HEqType well_typed.
    rewrite HEqType; move=> Convert; rewrite Convert; simpl.
    case_eq (find_val ctxt var).
    {
        discriminate.
    }
    {
        simpl.
        move=> _ _ <-; simpl.
        rewrite ident_beq_refl.
        reflexivity.
    }
Qed.

Goal
    forall arch prog type_ctxt ctxt opt_ctxt' var typ dir,
        find_val type_ctxt var = Some typ ->
        well_typed_ctxt type_ctxt ctxt ->
        convert_type typ nil = Some (dir, 2::nil) ->
        (exists v, eval_var (Index (Var var) (Const_e 0)) ctxt AAll = Some v) ->
        (exists v, eval_var (Index (Var var) (Const_e 1)) ctxt AAll = Some v) ->
        eval_deq arch prog type_ctxt ctxt
             (Eqn (Range (Var var) (Const_e 1) (Const_e 0)::nil) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                true) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = Some (CoIR dir (Some 2::Some 1::nil) (Some (2::nil))).
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
                    4,6: by discriminate.
                    1-3: by move=> a []; simpl; discriminate.
                    by move=> a []; discriminate.
                + discriminate.
                + move=> [|hd tl] HNeq.
                    - exfalso; apply HNeq; reflexivity.
                    - destruct d; destruct tl; discriminate.
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
            by destruct valoType.
        }
        destruct form.
        2: by destruct valoType.
        rewrite muln1 in valoType.
        destruct d.
        4: by discriminate.
        5: by discriminate.
        all: inversion Convert as [[HEq2 HEq3]]; clear Convert; simpl.
        all: destruct HEq2.
        all: symmetry in HEq3; destruct HEq3.
        all: destruct valoType as [simpl_eq [_ [length_eq dir_eq]]].
        all: rewrite length_eq; simpl.
        all: destruct l as [|h1 l].
        1,3,5,7: by discriminate.
        all: destruct l as [|h2 l].
        1,3,5,7: by discriminate.
        all: destruct l as [|].
        2,4,6,8: by discriminate.
        all: rewrite simpl_eq; simpl.
        all: destruct h1.
        2,4,6,8: by move=> []; discriminate.
        all: destruct h2.
        2,4,6,8: by move=> _ []; discriminate.
        all: simpl.
        all: move=> _ _ <-; simpl.
        all: rewrite ident_beq_refl.
        all: reflexivity.
    }
    {
        simpl.
        move=> _ []; discriminate.
    }
Qed.

