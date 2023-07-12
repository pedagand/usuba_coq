From mathcomp Require Import all_ssreflect.
Require Import ZArith.
From Usuba Require Import usuba_AST usuba_ASTProp arch semantic_base usuba_sem equiv_rel.

Goal
    forall arch prog type_ctxt ctxt opt_ctxt' var typ dir,
        find_val type_ctxt var = Some typ ->
        well_typed_ctxt type_ctxt ctxt ->
        convert_type typ = Some (dir, 1::nil) ->
        find_val ctxt var = None ->
        eval_deq arch prog type_ctxt ctxt
            (Eqn ((var, [:: IInd (Const_e 0%Z)]) :: (var, [:: IInd (Const_e 0%Z)]) :: nil) (Tuple (ECons (Const 1 None)
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
        convert_type typ = Some (dir, 1::nil) ->
        (exists v, eval_var (Index (Var var) [:: IInd (Const_e 0)]) ctxt = Some v) ->
        eval_deq arch prog type_ctxt ctxt
            (Eqn ((var, [:: IInd (Const_e 0%Z)]) :: (var, [:: IInd (Const_e 0%Z)]) :: nil) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                true) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = Some (CoIR dir (Some 2%Z::nil) (1::nil)).
Proof.
    simpl.
    unfold bind; unfold bind_aux_list.
    unfold bind_aux.
    simpl.
    move=> _ _ type_ctxt ctxt opt_ctxt var typ dir HEqType well_typed.
    rewrite HEqType; move=> Convert; rewrite Convert; simpl.
    unfold eval_var; simpl.
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
    update (2::nil) (Some 1::Some 2::nil)%Z (ASlice [:: 0] AAll) [:: CoIL 1] (DirH 8) true = Some (Some 1::Some 2::nil, nil)%Z.
Proof.
    simpl; reflexivity.
Qed.

Goal
    forall arch prog type_ctxt ctxt opt_ctxt' var typ dir,
        find_val type_ctxt var = Some typ ->
        well_typed_ctxt type_ctxt ctxt ->
        convert_type typ = Some (dir, 2::nil) ->
        find_val ctxt var = None ->
        eval_deq arch prog type_ctxt ctxt
             (Eqn ((var, [:: IRange (Const_e 1) (Const_e 0)])::nil) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                false) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = Some (CoIR dir (Some 2::Some 1::nil)%Z (2::nil)).
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

Require Import Lia.

Lemma divmod_change_rem:
    forall n p u q1 q2, (Nat.divmod n p q1 u).2 = (Nat.divmod n p q2 u).2.
Proof.
    move=> n; induction n as [|n HRec]; simpl; trivial.
    move=> p [|u] q1 q2; apply HRec.
Qed.

Lemma eq_divmod:
    forall n u q, (u < 2)%coq_nat -> (Nat.divmod n 1 q u).2 = (u + n) mod 2.
Proof.
    move=> n; induction n as [|n HRec]; simpl; trivial.
    {
        move=> u _; destruct u as [|[]]; simpl; auto.
        lia.
    }
    destruct (Nat.mod_bound_pos n 2); auto.
    by lia.
    move=> [|u] q Bound; rewrite HRec; trivial.
    1,3: lia.
    simpl.
    unfold addn_rec; rewrite Nat.add_succ_r; simpl.
    rewrite (divmod_change_rem _ _ _ 0 1); reflexivity.
Qed.

Goal
    forall arch prog type_ctxt ctxt opt_ctxt' var typ dir,
        find_val type_ctxt var = Some typ ->
        well_typed_ctxt type_ctxt ctxt ->
        convert_type typ = Some (dir, 2::nil) ->
        (exists v, eval_var (Index (Var var) [:: IInd (Const_e 0)]) ctxt = Some v) ->
        (exists v, eval_var (Index (Var var) [:: IInd (Const_e 1)]) ctxt = Some v) ->
        eval_deq arch prog type_ctxt ctxt
             (Eqn ((var, [:: IRange (Const_e 1) (Const_e 0)])::nil) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                true) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = Some (CoIR dir (Some 2::Some 1::nil)%Z (2::nil)).
Proof.
    simpl.
    unfold bind; unfold bind_aux_list.
    unfold bind_aux.
    simpl.
    move=> _ _ type_ctxt ctxt opt_ctxt var typ dir HEqType well_typed.
    unfold eval_var; simpl.
    rewrite HEqType; move=> Convert; rewrite Convert; simpl.
    case_eq (find_val ctxt var).
    {
        move=> c HEq.
        pose (p := well_typed_ctxt_imp_find_val _ _ _ _ well_typed HEq).
        destruct p as [typ' [find_typ valoType]].
        rewrite find_typ in HEqType; inversion HEqType as [HEq'].
        destruct HEq'; clear HEqType.
        destruct typ' as [|d m|typ ilen]; simpl in *.
        by discriminate.
        all: swap 1 2.
        {
            destruct typ as [|d m|typ len2]; simpl in *.
            by discriminate.
            {
                destruct m; destruct d; inversion Convert as [[Hdir Hilen]].
                all: destruct Hdir; symmetry in Hilen; destruct Hilen.
                all: destruct c.
                1,3,5,7,9-14: destruct valoType.
                all: destruct valoType as [H [NotEmpty [LengthEq DirEq]]]; symmetry in H; destruct H.
                4: by destruct DirEq.
                all: symmetry in LengthEq; destruct LengthEq; symmetry in DirEq; destruct DirEq.
                all: rewrite muln1; simpl.
                all: destruct l as [|h1 [|h2 []]].
                1,2,4-6,8-10,12: move=> H; destruct H as [v Abs]; inversion Abs.
                all: simpl; destruct h1 as [h1|].
                2,4,6: move=> H; destruct H as [v Abs]; inversion Abs.
                all: simpl; destruct h2 as [h2|].
                2,4,6: move=> _ H; destruct H as [v Abs]; inversion Abs.
                all: simpl; move=> _ _ <-; simpl; rewrite ident_beq_refl; reflexivity.
            }
            exfalso; move: Convert.
            pose (p := [:: len2; ilen]); fold p.
            assert (length p > 1) as NotEmpty
             by (unfold p; simpl; constructor).
            move: p NotEmpty; clear.
            induction typ as [|d m|typ HRec len']; simpl.
            by discriminate.
            {
                destruct m.
                + move=> []; destruct d; auto.
                    1-6: move=> a l HDiff HEq; inversion HEq as [[H H1 H2]].
                + discriminate.
                + move=> []; destruct d; auto.
                    1-6: move=> a l HDiff HEq; inversion HEq as [[H H1 H2]].
            }
            {
                move=> p NotEmpty.
                destruct convert_type as [[d l]|]; by idtac.
            }
        }
        simpl in *.
        destruct m as [| |].
        2,3: by destruct valoType.
        destruct c as [|d' l form]; simpl.
        by move=> [v H]; inversion H.
        destruct form.
        by move=> [v H]; inversion H.
        destruct valoType as [H1 [NotEmpty [length_eq dir_eq]]].
        move: HEq.
        inversion H1; clear H0 H2 H1 n1 form.
    }
    {
        simpl.
        move=> _ []; discriminate.
    }
Qed.

