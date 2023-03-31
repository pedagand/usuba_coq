From Usuba Require Import usuba_AST usuba_sem equiv_rel collect collectProof clean.
From Coq Require Import MSets MSets.MSetToFiniteSet MSets.MSetFacts.

From mathcomp Require Import all_ssreflect.
Require Import Coq.Sets.Ensembles.

Lemma clean_in_deqs_freevars:
    forall eqns vars x,
        iset.mem x (fst (clean_in_deqs vars (list_deq_of_deqL eqns))) = true <->
            iset.mem x vars = true \/
            In ident (deqs_vars (snd (clean_in_deqs vars (list_deq_of_deqL eqns)))) x.
Proof.
    move=> eqns; induction eqns as [|v e l tl HRec | i ae1 ae2 dL' HRec1 opt tl HRec2]; simpl.
    {
        split; auto.
        move => [|[]]; trivial.
    }
    {
        move=> vars x; specialize HRec with vars x.
        destruct (clean_in_deqs vars (list_deq_of_deqL tl)); simpl in *.
        case (iset.exists_ (iset.mem^~ t) (collect_varl v)); simpl; trivial.
        do 2 rewrite iset.mem_spec; do 2 rewrite iset.mem_spec in HRec.
        do 2 rewrite iset.union_spec; rewrite collect_expr_soundness.
        rewrite collect_varl_soundness.
        rewrite HRec; clear HRec; split.
        + move=> [[]|[]]; auto; move=> H; right.
            + constructor; assumption.
            + do 2 constructor; assumption.
            + do 2 constructor; assumption.
        + move=> [HIn|[elt' [elt HIn|elt HIn]|HIn]]; auto.
    }
    {
        move=> vars x; specialize HRec2 with vars x.
        destruct (clean_in_deqs vars (list_deq_of_deqL tl)) as [vars' tl']; simpl in *.
        case (iset.exists_ (iset.mem^~ vars') (collect_bounddeqs (list_deq_of_deqL dL')) || iset.mem i vars'); simpl; auto.
        rewrite iset.mem_spec; rewrite iset.add_spec; do 3 rewrite iset.union_spec; do 2 rewrite collect_aexpr_soundness.
        rewrite collect_deqs_soundness.
        rewrite iset.mem_spec in HRec2; rewrite HRec2; split.
        - move=> [|[[]|[[]|]]]; auto.
            * move=> ->; by do 3 constructor.
            * intros; right; constructor; assumption.
            * intros; right; do 3 constructor; assumption.
            * intros; right; do 4 constructor; assumption.
            * intros; right; do 4 constructor; assumption.
        - move=> [|[elt' [elt []|elt [|elt'2 []]]|]]; auto.
    }
Qed.

Lemma loop_rec_change_ctxt arch prog:
    forall e s body i ens ctxt1 ctxt2 type_ctxt,
        context_srel (Union ident (fun elt => iset.In elt (collect_deqs (list_deq_of_deqL body))) ens) ctxt1 ctxt2 ->
        opt_rel (context_srel (Union ident (fun elt => iset.In elt (collect_deqs (list_deq_of_deqL body))) ens))
            (loop_rec ctxt1 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i s e)
            (loop_rec ctxt2 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i s e).
Proof.
    move=> e; induction e as [|e HRec]; simpl; auto.
    move=> s body i ens ctxt1 ctxt2 type_ctxt HRel.
    case (match s with 0 => false | m'.+1 => PeanoNat.Nat.leb e m' end); simpl; auto.
    pose (p := HRec s body i ens ctxt1 ctxt2 type_ctxt HRel); move:p.
    destruct (loop_rec ctxt1 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i s e).
    all: destruct (loop_rec ctxt2 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i s e); simpl; auto.
    2: move=> [].
    2: discriminate.
    move=> HRel2.
    apply eval_deqL_change_ctxt.
    {
        reflexivity.
    }
    {
        move=> elt HIn.
        constructor 1.
        unfold In.
        rewrite collect_deqs_soundness.
        assumption.
    }
    {
        move=> elt HIn; simpl.
        case (String.eqb elt i); trivial.
        apply HRel2; assumption.
    }
Qed.

Lemma clean_in_deqs_soundness arch prog:
    forall eqns vars ctxt1 ctxt2 type_ctxt,
        eval_deq_list arch prog type_ctxt ctxt1 (list_deq_of_deqL eqns) <> None ->
        context_srel (deqs_vars (snd (clean_in_deqs vars (list_deq_of_deqL eqns)))) ctxt1 ctxt2 ->
        context_srel (fun i => iset.mem i vars = true) ctxt1 ctxt2 ->
        opt_rel (context_srel (fun i => iset.mem i vars = true))
            (eval_deq_list arch prog type_ctxt ctxt1 (list_deq_of_deqL eqns))
            (eval_deq_list arch prog type_ctxt ctxt2 (snd (clean_in_deqs vars (list_deq_of_deqL eqns)))).
Proof.
    move=> eqns; induction eqns as [|v expr b tl HRec'|i aei1 aei2 body HRecBody opt tl HRecTL]; simpl.
    { auto. }
    {
        move=> vars ctxt1 ctxt2 type_ctxt.
        pose (p := clean_in_deqs_freevars tl vars); move:p.
        pose (HRec := HRec' vars); move: HRec.
        destruct (clean_in_deqs vars (list_deq_of_deqL tl)) as [vars' tl']; simpl in *.
        clear HRec'.
        case_eq (iset.exists_ (iset.mem^~ vars') (collect_varl v)); simpl.
        {
            move=> _ HRec _ HnoErr HRel1 HRel2.
            rewrite <- (eval_expr_change_ctxt _ _ ctxt1 ctxt2 prog prog).
            + destruct (eval_expr arch prog ctxt1 expr) as [val|]; simpl; trivial.
                assert (context_srel (Union ident (varl_freevars v)
                    (Union ident (deqs_vars tl') (fun i : ident => iset.mem i vars = true))) ctxt1 ctxt2) as HRel3.
                {
                    move=> x HIn; destruct HIn as [|x []].
                    - apply HRel1; do 2 constructor; assumption.
                    - apply HRel1; constructor; assumption.
                    - apply HRel2; assumption.
                }
                pose (H := context_srel_bind v type_ctxt _ _ val _ HRel3); move: H.
                destruct (bind ctxt1 type_ctxt v val) as [ctxt1'|]; simpl.
                2: by move=> ->; simpl; reflexivity.
                destruct (bind ctxt2 type_ctxt v val) as [ctxt2'|]; simpl.
                2: by move=> [].
                move=> HRel4; apply HRec; trivial.
                - move=> x HIn; apply HRel4; do 2 constructor; assumption.
                - move=> x HIn; apply HRel4; do 2 constructor; assumption.
            + reflexivity.
            + move=> x HIn; apply HRel1; do 2 constructor; assumption.
        }
        {
            rewrite <- not_true_iff_false.
            rewrite iset.exists_spec.
            move=> NegExists HRec Hfreevars HnoErr HRel1 HRel2.
            case (eval_expr arch prog ctxt1 expr) as [x|].
            2: exfalso; apply HnoErr; reflexivity.
            pose (p := context_srel_bind_compl v x ctxt1 type_ctxt); move:p.
            case (bind ctxt1 type_ctxt v x) as [ctxt'|].
            2: exfalso; apply HnoErr; reflexivity.
            move=> HRel3; apply HRec; trivial.
            all: transitivity ctxt1; trivial.
            all: symmetry; move=> elt HIn; apply HRel3.
            all: assert (iset.mem elt vars' = true) as Hfreevars' by (rewrite Hfreevars; auto).
            all: clear Hfreevars; unfold Complement; unfold In; move=> HIn'.
            all: apply NegExists; unfold iset.Exists; exists elt; split; trivial.
            all: rewrite collect_varl_soundness; unfold In; assumption.
        }
    }
    {
        move=> vars ctxt1 ctxt2 type_ctxt HnoErr HRel1 HRel2.
        pose (p := clean_in_deqs_freevars tl vars); move:p.
        pose (p := HRecTL vars); move: p; clear HRecTL.
        destruct (clean_in_deqs vars (list_deq_of_deqL tl)) as [vars' tl']; simpl.
        move=> HRecTL.
        case_eq (iset.exists_ (iset.mem^~ vars') (collect_bounddeqs (list_deq_of_deqL body))
            || iset.mem i vars').
        all: move=> HEq; rewrite HEq in HRel1; simpl.
        {
            move=> _; clear HEq; move: HnoErr.
            rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
            2: apply context_srel_imp_context_csrel; move=> x HIn; apply HRel1; simpl; do 3 constructor; assumption.
            rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
            2: apply context_srel_imp_context_csrel; move=> x HIn; apply HRel1; simpl; do 4 constructor; assumption.
            destruct (eval_arith_expr ctxt2 aei1) as [s|]; simpl; trivial.
            destruct (eval_arith_expr ctxt2 aei2) as [e|]; simpl; trivial.
            assert (context_srel (Union ident (iset.In^~ (collect_deqs (list_deq_of_deqL body)))
               (Union ident (fun i : ident => iset.mem i vars = true) (deqs_vars tl'))) ctxt1 ctxt2) as HRel3.
            {
                move=> x' [x HIn|x'' [x HIn|x HIn]].
                + apply HRel1; simpl; unfold In in HIn; rewrite collect_deqs_soundness in HIn.
                    do 4 constructor; assumption.
                + apply HRel2; assumption.
                + apply HRel1; simpl; constructor; assumption. 
            }
            pose (p := loop_rec_change_ctxt arch prog e s body i _ ctxt1 ctxt2 type_ctxt HRel3); move: p; clear HRel3.
            destruct (loop_rec ctxt1 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i s e) as [ctxt1'|].
            2: move=> _ HnoErr; exfalso; apply HnoErr; reflexivity.
            destruct (loop_rec ctxt2 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i s e) as [ctxt2'|]; simpl.
            2: move=> [].
            assert (match find_val ctxt1 i with Some v => Some ((i, v) :: ctxt1') | None => Some ctxt1' end
                = Some match find_val ctxt1 i with Some v => (i, v)::ctxt1' | None => ctxt1' end) as HEq
                by (case (find_val ctxt1 i); simpl; auto).
            rewrite HEq; clear HEq.
            assert (match find_val ctxt2 i with Some v => Some ((i, v) :: ctxt2') | None => Some ctxt2' end
                = Some match find_val ctxt2 i with Some v => (i, v)::ctxt2' | None => ctxt2' end) as HEq
                by (case (find_val ctxt2 i); simpl; auto).
            rewrite HEq; clear HEq.
            move=> HRel3 HnoErr.
            apply HRecTL; auto; move=> x HIn; case_eq (String.eqb x i).
            1,3: rewrite String.eqb_eq; move=> HEq; destruct HEq.
            {
                assert (find_val ctxt1 x = find_val ctxt2 x) as HEq
                    by (apply HRel1; simpl; constructor; assumption); destruct HEq.
                case (find_val ctxt1 x); simpl.
                + rewrite String.eqb_refl; reflexivity.
                + apply HRel3; do 2 constructor; assumption.
            }
            {
                assert (find_val ctxt1 x = find_val ctxt2 x) as HEq
                    by (apply HRel2; simpl; assumption); destruct HEq.
                case (find_val ctxt1 x); simpl.
                + rewrite String.eqb_refl; reflexivity.
                + apply HRel3; do 2 constructor; assumption.
            }
            all: case (find_val ctxt1 i); case (find_val ctxt2 i); simpl.
            1,5: move=> v v' ->.
            3,4,6,7: move=> v ->.
            7,8: move=> _.
            all: apply HRel3; do 2 constructor; assumption.
        }
        {
            rewrite orb_false_iff in HEq; destruct HEq as [Hexists HnegMem].
            destruct (eval_arith_expr ctxt1 aei1) as [i1|].
            2: exfalso; apply HnoErr; reflexivity.
            destruct (eval_arith_expr ctxt1 aei2) as [i2|].
            2: exfalso; apply HnoErr; reflexivity.
            pose (p := loop_rec_unchanged_ctxt arch prog i i1 i2 body ctxt1 type_ctxt); move:p.
            destruct (loop_rec ctxt1 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt'|].
            2: exfalso; apply HnoErr; reflexivity.
            clear HRecBody.
            move=> HRel Hvars'.
            case_eq (find_val ctxt1 i).
            1: move=> v Hfind_val; rewrite Hfind_val in HnoErr.
            2: move=> Hfind_val; rewrite Hfind_val in HnoErr.
            all: apply HRecTL; trivial; transitivity ctxt1; trivial; symmetry.
            all: move=> elt HIn; simpl.
            {
                case_eq (String.eqb elt i).
                + rewrite String.eqb_eq; move=> HEq2; destruct HEq2; assumption.
                + move=> HnotEq; apply HRel; unfold Complement, In; move=> HIn'.
                    rewrite <- not_true_iff_false in Hexists; apply Hexists.
                    rewrite iset.exists_spec; unfold iset.Exists.
                    exists elt.
                    destruct HIn' as [elt' []|].
                    by rewrite String.eqb_refl in HnotEq.
                    rewrite collect_bounddeqs_soundness_lemma; split; trivial.
                    rewrite Hvars'; auto.
            }
            {
                case_eq (String.eqb elt i).
                + rewrite String.eqb_eq; move=> HEq2; destruct HEq2; assumption.
                + move=> HnotEq; apply HRel; unfold Complement, In; move=> HIn'.
                    rewrite <- not_true_iff_false in Hexists; apply Hexists.
                    rewrite iset.exists_spec; unfold iset.Exists.
                    exists elt.
                    destruct HIn' as [elt' []|].
                    by rewrite String.eqb_refl in HnotEq.
                    rewrite collect_bounddeqs_soundness_lemma; split; trivial.
                    rewrite Hvars'; auto.
            }
            all: rewrite <- not_true_iff_false in HnegMem; rewrite Hvars' in HnegMem.
            all: apply HRel; unfold Complement, In; move=> HIn'; destruct HIn' as [elt' []|elt' HIn'].
            1,3: apply HnegMem; auto.
            all: rewrite <- not_true_iff_false in Hexists; apply Hexists.
            all: rewrite iset.exists_spec; unfold iset.Exists.
            all: exists elt'.
            all: rewrite Hvars'; split; auto.
            all: rewrite collect_bounddeqs_soundness_lemma; trivial.
        }
    }
Qed.

Theorem clean_node_soudness arch prog:
    forall node param input,
        eval_node node arch prog param input <> None ->
        eval_node node arch prog param input =
        eval_node (clean_node node) arch prog param input.
Proof.
    unfold clean_node.
    move=> [id p_in p_out node_opt [temp_vars eqns| | |]]; simpl; trivial.
    unfold eval_node; simpl.
    move=> [] input; trivial.
    case (build_ctxt p_in input); trivial.
    move=> ctxt HnoErr.
    assert (eval_deq_list arch prog (build_type_ctxt (temp_vars ++ p_in ++ p_out)) ctxt eqns <> None) as HnoErr1.
    {
        move=> HEq; rewrite HEq in HnoErr; apply HnoErr; trivial.
    }
    pose (p := clean_in_deqs_soundness arch prog (deqL_of_list_deq eqns) (collect_vdecl p_out) ctxt ctxt); move: p.
    rewrite deqL_is_list_deq; move=> p.
    pose (p' := p (build_type_ctxt (_ ++ _ ++ _)%list) HnoErr1 (context_srel_refl _ _) (context_srel_refl _ _)); move: p'; clear p.
    destruct (eval_deq_list arch prog _ ctxt eqns); simpl.
    2: by move=> ->; trivial.
    destruct (eval_deq_list arch prog _ ctxt (snd (clean_in_deqs (collect_vdecl p_out) eqns))); simpl.
    {
        induction p_out as [|a tl HRec]; simpl; trivial.
        move=> HRel; rewrite HRec.
        + rewrite HRel; trivial.
            unfold Ensembles.In; rewrite iset.mem_spec; rewrite iset.add_spec; auto.
        + simpl in HnoErr; move=> HEq; rewrite HEq in HnoErr; apply HnoErr; case (find_val c (VD_ID a)); trivial.
        + move=> x HIn; apply HRel; unfold Ensembles.In in *.
            rewrite iset.mem_spec; rewrite iset.mem_spec in HIn; rewrite iset.add_spec; auto.
    }
    {
        move=> [].
    }
Qed.
