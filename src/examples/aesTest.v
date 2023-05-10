Require Import ZArith.
From mathcomp Require Import seq.
From Usuba Require Import arch utils usuba_ASTProp usuba_sem usuba_semProp aes.
Require Import Lia.

Ltac simpl_1 iL Abs :=
    let h := fresh "hd" in
    destruct iL as [|h iL];
    [> discriminate Abs | simpl in Abs].

Definition list_d4 : list Z := [:: 1; 1; 0; 1; 0; 1; 0; 0].
Definition list_bf : list Z := [:: 1; 0; 1; 1; 1; 1; 1; 1].
Definition list_5d : list Z := [:: 0; 1; 0; 1; 1; 1; 0; 1].
Definition list_30 : list Z := [:: 0; 0; 1; 1; 0; 0; 0; 0].
Definition list_04 : list Z := [:: 0; 0; 0; 0; 0; 1; 0; 0].
Definition list_cb : list Z := [:: 1; 1; 0; 0; 1; 0; 1; 1].
Definition list_19 : list Z := [:: 0; 0; 0; 1; 1; 0; 0; 1].
Definition list_9a : list Z := [:: 1; 0; 0; 1; 1; 0; 1; 1].

Ltac gen_notation_inner a :=
    lazymatch a with
    | match ?b with Some _ => _ | None => _ end => gen_notation_inner b
    | _ => let H := fresh "H" in pose (H := a)
    end.

Ltac gen_notation :=
    lazymatch goal with
    | |- ?g = _ => gen_notation_inner g
    | |- ?g <> _ => gen_notation_inner g
    end.

(* Theorem
    eval_expr prog_tl4 [:: (Id_s "v", CoIR DirB (list_d4 ++ list_bf ++ list_5d ++ list_30) (Some [:: 4; 8]))]
    = Some (CoIR DirB ) *)

Goal
    prog_sem default_arch prog_tl7 None [:: CoIR DirB (
        list_d4 ++ list_d4 ++ list_d4 ++ list_d4 ++
        list_d4 ++ list_d4 ++ list_d4 ++ list_d4 ++
        list_d4 ++ list_d4 ++ list_d4 ++ list_d4 ++
        list_d4 ++ list_d4 ++ list_d4 ++ list_d4) (16%nat::8%nat::nil)]
    <> None.
Proof.
    cbn - [build_ctxt_aux].
    unfold build_ctxt_aux.
    gen_notation.
    unfold loop_rec.
    cbn.
    unfold Pos.to_nat.
    cbn - [eval_var].
    gen_notation.
    unfold eval_var.
    cbn - [eval_var_inner].
    gen_notation.
    unfold eval_var; cbn - [remove_option_from_list].
    unfold remove_option_from_list.
    unfold eval_node.
    cbn - [eval_node_inner].
    gen_notation.
    unfold try_take_n.
    unfold SIZE_MONO, DIR_MONO.
    gen_notation.
    gen_notation.
    cbn - [bind].

Theorem node_MixColumn_single_test:
    prog_sem default_arch prog_tl3 None [:: CoIR DirB (list_d4 ++ list_bf ++ list_5d ++ list_30) (4%nat::8%nat::nil)]
    = Some [:: CoIR DirB (list_04 ++ list_cb ++ list_19 ++ list_9a) [:: 4%nat; 8%nat]].
Proof.
    cbn - [prog_tl4].
    unfold eval_node; cbn - [prog_tl4].
    unfold Pos.to_nat; cbn - [prog_tl4].
    cbn - [times2].
    cbn; unfold eval_node; cbn.
    unfold Pos.to_nat; cbn.
    unfold bind; cbn.
    unfold Pos.to_nat; cbn.
    gen_notation.

Theorem build_ctxt_lemma:
    forall n name args_tl iL iL_tl,
        length iL = n ->
        iL_tl <> nil ->
        build_ctxt ((name : (Uint Bslice (Mint 1) n))%ua_var_decl :: args_tl) (CoIR DirB (iL ++ iL_tl) None:: nil) =
        match build_ctxt args_tl (CoIR DirB iL_tl None:: nil) with
        | None => None
        | Some ctxt => Some ((name, CoIR DirB (map Some iL) (Some (n::nil)))::ctxt)
        end.
Proof.
    intros n name args_tl iL iL_tl LengthEq NotNil; simpl.
    do 2 rewrite muln1; rewrite try_take_n_soundness; auto.
    destruct iL_tl as [|hd tl]; [> exfalso; apply NotNil; reflexivity | idtac].
    pose (iL_tl := hd::tl); fold iL_tl; generalize iL_tl; clear iL_tl; intro iL_tl.
    destruct n; simpl; trivial.
    destruct iL; auto; discriminate.
Qed.

Theorem build_ctxt_lemma2:
    forall n name iL,
        length iL = n ->
        n <> 0 ->
        build_ctxt ((name : (Uint Bslice (Mint 1) n))%ua_var_decl :: nil) (CoIR DirB iL None:: nil) =
        Some ((name, CoIR DirB (map Some iL) (Some (n::nil)))::nil).
Proof.
    intros n name iL LengthEq NotZero; simpl.
    do 2 rewrite muln1; rewrite try_take_n_all; auto.
    destruct n; [> exfalso; apply NotZero; reflexivity | idtac].
    reflexivity.
Qed.

Theorem build_ctxt_lemma2_arrray:
    forall m n name iL,
        length iL = n * m ->
        n * m <> 0 ->
        build_ctxt ((name : (Uint Bslice (Mint 1) n [m]))%ua_var_decl :: nil) (CoIR DirB iL None:: nil) =
        Some ((name, CoIR DirB (map Some iL) (Some (m::n::nil)))::nil).
Proof.
    intros m n name iL LengthEq NotZero; simpl.
    do 2 rewrite muln1; rewrite try_take_n_all; auto.
    unfold muln, muln_rec.
    destruct (n * m); [> exfalso; apply NotZero; reflexivity | idtac].
    reflexivity.
Qed.

Theorem add_roundkey_soundness:
    forall l1 l2,
    length l1 = 128 -> length l2 = 128 ->
    exists l,
        eval_node default_arch node_AddRoundKey (eval_prog default_arch prog_tl2) None (CoIR DirB (seq.cat l1 l2) None::nil) = Some (CoIR DirB l (Some (128::nil))::nil) /\
        length l = 128.
Proof.
    intros l1 l2 length1 length2.
    unfold node_AddRoundKey, eval_node, P_IN, P_OUT, NODE.
    unfold b128, infer_types, VD_TYP, convert_type, IntSize_of_nat.
    unfold seq.cat, prod_list; fold (@seq.cat nat).
    rewrite ssrnat.muln1.
    do 128 simpl_1 l1 length1.
    destruct l1; [> clear length1 | discriminate length1].
    cbn.
    do 128 simpl_1 l2 length2.
    destruct l2; [> clear length2 | discriminate length2].
    cbn.
    eexists.
    split.
    reflexivity.
    cbn; reflexivity.
Qed.

Theorem undefined_slice_0:
    forall n1 n2 (l : list nat),
        n1 <> 0 ->
        n2 <> 0 ->
        length l = n2 ->
        update (n1 :: n2 :: nil) 
            (undefined (prod_list (n1 :: n2 :: nil))) 
            (ASlice (0 :: nil) AAll)
            (CoIR DirB l (Some (n2::nil)) :: nil) DirB false 
        = Some (map Some l ++ undefined ((n1 - 1) * n2), nil).
Proof.
    intros n1 n2 l NotZero NotZero2 length_eq.
    simpl.
    rewrite ssrnat.muln1.
    rewrite length_undefined.
    unfold ssrnat.muln, ssrnat.muln_rec.
    rewrite PeanoNat.Nat.mul_comm.
    rewrite PeanoNat.Nat.mod_mul; auto.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite PeanoNat.Nat.mul_1_r.
    simpl.
    rewrite split_into_segments_undefined.
    destruct n1 as [|n1].
    1: exfalso; apply NotZero; reflexivity.
    simpl; rewrite length_undefined.
    rewrite PeanoNat.Nat.mod_same; auto.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite split_into_segments_1_r; auto.
    2: rewrite length_undefined; reflexivity.
    destruct n2 as [|n2].
    1: exfalso; apply NotZero2; reflexivity.
    rewrite try_take_n_all; auto.
    simpl.
    do 3 f_equal.
    rewrite PeanoNat.Nat.mul_comm.
    rewrite <- undefined_lemma.
    rewrite PeanoNat.Nat.sub_0_r.
    auto.
Qed.

Goal
    forall l, l = (0::1::0::1::0::1::1::1::nil) ->
        eval_node default_arch node_subBytes_single nil
            None (CoIR DirB l None::nil)
        <> None.
Proof.
    intros n Hlen.
    symmetry in Hlen; destruct Hlen.
    cbn.
    discriminate.
Qed.

Theorem node_subBytes_single_soudness:
    forall l, length l = 8 ->
        Forall (fun i => i = 0 \/ i = 1) l ->
        exists l', eval_node default_arch node_subBytes_single nil
            None (CoIR DirB l None::nil) = Some (CoIR DirB l' (Some (8::nil))::nil) /\ length l' = 8 /\
            Forall (fun i => i = 0 \/ i = 1) l'.
Proof. admit. Admitted.


Ltac gen_notation_inner a :=
    lazymatch a with
    | match ?b with Some _ => _ | None => _ end => gen_notation_inner b
    | _ => let H := fresh "H" in pose (H := a)
    end.

Ltac gen_notation :=
    lazymatch goal with
    | |- ?g <> None => gen_notation_inner g
    end.

Goal
    forall l, length l = 8 * 16 ->
        Forall (fun i => i = 0 \/ i = 1) l ->
        eval_node default_arch node_subbytes (eval_prog default_arch prog_tl8)
            None (CoIR DirB l None::nil) 
        <> None.
Proof.
    intros l length_eq HForall.
    cbn in length_eq.
    unfold eval_node, node_subbytes, P_IN, P_OUT, NODE, b8.
    unfold infer_types, VD_TYP, convert_type, eval_arith_expr, IntSize_of_nat, seq.cat.
    unfold prod_list.
    do 128 simpl_1 l length_eq.
    destruct l; [> clear length_eq | discriminate].
    cbn - [eval_node_inner  eval_node].
    cbn - [eval_deq_list eval_node].
    cbn - [eval_deq eval_node].
    unfold eval_deq, eval_arith_expr, find_val.
    fold (@find_val (@cst_or_int (option nat))).
    cbn - [find_val eval_node].
    cbn - [remove_option_from_list eval_node].
    unfold remove_option_from_list, seq.cat.
    fold (@remove_option_from_list nat).
    do 128 rewrite Forall_cons_iff in HForall.
    repeat let H := fresh "for" in destruct HForall as [H HForall].
    clear HForall.
    unfold linearize_list_value; fold (@linearize_list_value nat).
    pose (p := node_subBytes_single_soudness (hd::hd0::hd1::hd2::hd3::hd4::hd5::hd6::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall1]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd7::hd8::hd9::hd10::hd11::hd12::hd13::hd14::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall2]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd15::hd16::hd17::hd18::hd19::hd20::hd21::hd22::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall3]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd23::hd24::hd25::hd26::hd27::hd28::hd29::hd30::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall4]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd31::hd32::hd33::hd34::hd35::hd36::hd37::hd38::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall5]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd39::hd40::hd41::hd42::hd43::hd44::hd45::hd46::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall6]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd47::hd48::hd49::hd50::hd51::hd52::hd53::hd54::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall7]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd55::hd56::hd57::hd58::hd59::hd60::hd61::hd62::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall8]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd63::hd64::hd65::hd66::hd67::hd68::hd69::hd70::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall9]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd71::hd72::hd73::hd74::hd75::hd76::hd77::hd78::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall10]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd79::hd80::hd81::hd82::hd83::hd84::hd85::hd86::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall11]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd87::hd88::hd89::hd90::hd91::hd92::hd93::hd94::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall12]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd95::hd96::hd97::hd98::hd99::hd100::hd101::hd102::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall13]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd103::hd104::hd105::hd106::hd107::hd108::hd109::hd110::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall14]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd111::hd112::hd113::hd114::hd115::hd116::hd117::hd118::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall15]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].

    pose (p := node_subBytes_single_soudness (hd119::hd120::hd121::hd122::hd123::hd124::hd125::hd126::nil)).
    generalize p; clear p.
    impl_tac. { cbn; reflexivity. }
    impl_tac. { repeat (constructor; trivial). }
    intro H; destruct H as [l1 [-> [Hlength1 HForall16]]].
    cbn - [eval_node].
    do 8 simpl_1 l1 Hlength1.
    destruct l1; [> clear Hlength1 | discriminate].
    cbn - [eval_node].
    discriminate.
Qed.

Goal
    forall l1 l2,
        length l1 = 128 -> length l2 = 11 * 128 ->
        prog_sem default_arch prog None (CoIR DirB (l1 ++ l2) None::nil) <> None.
Proof.
    unfold prog, prog_sem, eval_prog; fold eval_prog.
    unfold node_AES, eval_node, P_IN, P_OUT, NODE.
    unfold subst_infer_p, b128, VD_ID, VD_TYP, VD_OPTS, subst_infer_def.
    unfold subst_infer_list_deq, subst_infer_deq, subst_infer_expr.
    unfold infer_types, b128, VD_TYP, convert_type, IntSize_of_nat, DIR_MONO, SIZE_MONO.
    unfold eval_arith_expr, seq.cat; fold (@seq.cat nat).
    unfold subst
    unfold eval_node_inner.
    pose (prog_ctxt := eval_prog default_arch prog_tl); fold prog_ctxt.
    intros l1 l2 length1 length2.
    unfold b128.
    rewrite build_ctxt_lemma; trivial.
    rewrite build_ctxt_lemma2_arrray; trivial.
    2: simpl; discriminate.
    2: destruct l2; simpl in *; discriminate.
    unfold seq.cat, build_type_ctxt, eval_deq_list.
    unfold VD_ID, VD_TYP.
    unfold eval_arith_expr, eval_expr; fold eval_expr.
    unfold eval_var, find_val; fold (@find_val (@cst_or_int (option nat))).
    fold (@find_val node_sem_type).
    unfold plain, key, ident_beq, internal_string_beq, internal_ascii_beq, internal_bool_beq, andb.
    fold plain; fold key.
    rewrite get_access_AAll; auto.
    unfold eval_arith_expr.
    unfold get_access; rewrite map_length; rewrite length2.
    rewrite PeanoNat.Nat.mul_comm.
    rewrite PeanoNat.Nat.mod_mul; auto.
    rewrite PeanoNat.Nat.div_mul; auto.
    rewrite PeanoNat.Nat.eqb_refl.
    pose (p := split_into_segments_soundness2 11 128 l2); generalize p; clear p.
    impl_tac.
    {
        unfold ssrnat.muln, ssrnat.muln_rec; assumption.
    }
    intro H; destruct H as [l2' [split_eq [HForall [HEq length_eq]]]].
    rewrite split_eq.
    destruct HEq.
    pose (l2 := l2').
    do 11 simpl_1 l2' length_eq.
    destruct l2'; [> clear length_eq | discriminate length_eq].
    clear length2.
    inversion HForall  as [|h0 tl length_h0 HForall' H1]; destruct H1; clear HForall  H tl.
    inversion HForall' as [|h1 tl length_h1 HForall  H1]; destruct H1; clear HForall' H tl.
    inversion HForall  as [|h2 tl length_h2 HForall' H1]; destruct H1; clear HForall  H tl.
    inversion HForall' as [|h3 tl length_h3 HForall  H1]; destruct H1; clear HForall' H tl.
    inversion HForall  as [|h4 tl length_h4 HForall' H1]; destruct H1; clear HForall  H tl.
    inversion HForall' as [|h5 tl length_h5 HForall  H1]; destruct H1; clear HForall' H tl.
    inversion HForall  as [|h6 tl length_h6 HForall' H1]; destruct H1; clear HForall  H tl.
    inversion HForall' as [|h7 tl length_h7 HForall  H1]; destruct H1; clear HForall' H tl.
    inversion HForall  as [|h8 tl length_h8 HForall' H1]; destruct H1; clear HForall  H tl.
    inversion HForall' as [|h9 tl length_h9 HForall  H1]; destruct H1; clear HForall' H tl.
    inversion HForall  as [|h10 tl length_h10 HForall' H1]; destruct H1; clear HForall HForall' H tl.
    clear split_eq l2.
    cbn - [ prog_ctxt ].
    assert (find_val prog_ctxt AddRoundKey = Some (eval_node default_arch node_AddRoundKey (eval_prog default_arch prog_tl2))) as HEq.
    {
        unfold prog_ctxt, prog_tl; fold prog_tl2.
        unfold eval_prog; fold eval_prog.
        unfold find_val, node_AddRoundKey, ID.
        rewrite ident_beq_refl.
        reflexivity.
    }
    rewrite HEq; clear HEq.
    cbn - [prog_ctxt].

    pose (h0b := h0).
    do 128 simpl_1 h0 length_h0.
    destruct h0; [> clear length_h0 | discriminate].
    cbn - [prog_ctxt].

    pose (l1' := l1).
    do 128 simpl_1 l1 length1.
    destruct l1; [> clear length1 | discriminate length1].
    cbn - [prog_ctxt].

    cbn.

    pose (p := add_roundkey_soundness l1' h0b).
    unfold h0b,l1' in p.
    destruct (p) as [h0' [-> length_h0']]; auto.

    simpl.
    do 128 simpl_1 h1.
    destruct h1; [> idtac | discriminate].
    do 128 simpl_1 h2.
    destruct h2; [> idtac | discriminate].
    do 128 simpl_1 h3.
    destruct h3; [> idtac | discriminate].
    clear split_eq length_h0 length_h1 length_h2 length_h3 l2.
    simpl.
    do 128 simpl_1 h4.
    destruct h4; [> idtac | discriminate].
    do 128 simpl_1 h5.
    destruct h5; [> idtac | discriminate].
    do 128 simpl_1 h6.
    destruct h6; [> idtac | discriminate].
    do 128 simpl_1 h7.
    destruct h7; [> idtac | discriminate].
    do 128 simpl_1 h8.
    destruct h8; [> idtac | discriminate].
    do 128 simpl_1 h9.
    destruct h9; [> idtac | discriminate].
    do 128 simpl_1 h10.
    destruct h10; [> idtac | discriminate].
    clear.
    assert (forall l, (seq.map (fun i : nat =>
        nth_error (map (map Some) (h0 :: l)) i) (0 :: nil))
        = Some (map Some h0)::nil) as HEq by auto.
    rewrite HEq; clear HEq.
    unfold fold_right; fold fold_right.
    rewrite map_length; rewrite length_h0.
    rewrite PeanoNat.Nat.mod_same; auto.
    rewrite PeanoNat.Nat.eqb_refl; rewrite PeanoNat.Nat.div_same; auto.
    rewrite split_into_segments_1_r.
    2: rewrite map_length; exact length_h0.
    rewrite remove_option_from_list_map_Some.
    unfold linearize_list_value; fold (@linearize_list_value nat).
    unfold dir_beq.
    assert (find_val prog_ctxt AddRoundKey = Some (eval_node default_arch node_AddRoundKey (eval_prog default_arch prog_tl2))) as HEq.
    {
        unfold prog_ctxt, prog_tl; fold prog_tl2.
        unfold eval_prog; fold eval_prog.
        unfold find_val, node_AddRoundKey, ID.
        rewrite ident_beq_refl.
        reflexivity.
    }
    rewrite HEq; clear HEq.
    rewrite seq.cats0.
    unfold prog_ctxt, find_val; fold (@find_val (@cst_or_int (option nat))).
    destruct (add_roundkey_soundness l1 h0) as [h0' [-> length_h0']]; trivial.
    unfold linearize_list_value; fold (@linearize_list_value nat).
    unfold bind, bind_aux_list, bind_aux; fold bind_aux.
    unfold find_val; fold (@find_val typ); fold (@find_val node_sem_type).
    rewrite ident_beq_refl.
    unfold convert_type, eval_arith_expr, IntSize_of_nat.
    assert (ident_beq tmp key = false) as HNeq_tmp_key by auto.
    assert (ident_beq tmp plain = false) as HNeq_tmp_plain by auto.
    assert (ident_beq tmp i = false) as HNeq_tmp_i by auto.
    rewrite HNeq_tmp_key; rewrite HNeq_tmp_plain.
    unfold seq.cat.
    rewrite undefined_slice_0; auto.
    unfold loop_rec, PeanoNat.Nat.leb.
    unfold find_const; rewrite ident_beq_refl.
    rewrite HNeq_tmp_i.

    
    fold bind_aux_list.


Qed.
