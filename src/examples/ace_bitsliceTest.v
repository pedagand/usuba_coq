
Require Import ZArith String List.
From Usuba Require Import arch utils usuba_AST usuba_ASTProp usuba_sem usuba_semProp ace_bitslice.
Require Import Lia.

Lemma node_f_soundness:
    forall x,
        exists v, eval_node default_arch node_f nil None (CoIR (DirV (32%nat)) (x::nil) nil::nil)
            = Some (CoIR (DirV 32%nat) (v::nil) nil::nil).
Proof.
    intro x.
    unfold prog_sem.
    cbn - [eval_expr].
    unfold eval_expr, eval_var, eval_arith_expr.
    cbn - [eval_shift].
    unfold eval_shift, shift_wrapper, default_arch, IMPL_SHIFT.
    pose (p := lrotate 32 (Pos.to_nat 5) x); fold p.
    unfold Pos.to_nat; cbn.
    eexists; reflexivity.
Qed.

Ltac simpl_1 iL Abs :=
    let h := fresh "hd" in
    destruct iL as [|h iL];
    [> discriminate Abs | simpl in Abs].


Ltac gen_notation_inner a :=
    lazymatch a with
    | match ?b with Some _ => _ | None => _ end => gen_notation_inner b
    | _ => let H := fresh "H" in pose (H := a)
    end.

Ltac gen_notation :=
    lazymatch goal with
    | |- ?g <> None => gen_notation_inner g
    end.


Ltac simpl_util_inner a :=
    lazymatch a with
    | match ?b with Some _ => _ | None => _ end => simpl_util_inner b
    | eval_node _ _ nil None (CoIR _ (?e::nil) _::_) =>
        let v := fresh "v" in
        destruct (node_f_soundness e) as [v ->]
    | _ => let H := fresh "H" in pose (H := a)
    end.

Ltac simpl_util :=
    lazymatch goal with
    | |- exists v1 v2, ?g = _ => simpl_util_inner g
    end.

Lemma node_simeck_box_soundness:
    forall iL, length iL = 3%nat ->
        exists v1 v2,
            eval_node default_arch node_simeck_box ((ident.Id_s syntax.f, eval_node default_arch node_f nil)::nil) None (CoIR (DirV 32%nat) iL (3%nat::nil)::nil)
            = Some (CoIR (DirV 32%nat) (v1::v2::nil) (2%nat::nil)::nil).
Proof.
    intros iL Hlength.
    do 3 simpl_1 iL Hlength.
    destruct iL; [> clear Hlength | discriminate Hlength].
    cbn - [node_f].
    unfold bind.
    cbn - [eval_node].
    unfold Pos.to_nat.
    cbn - [eval_node].
    destruct (node_f_soundness hd) as [v1 ->].
    cbn - [eval_node].
    unfold Pos.to_nat.
    cbn - [eval_node].
    unfold Pos.to_nat.
    cbn - [eval_node].
    unfold eval_var; cbn - [remove_option_from_list ].
    unfold Pos.to_nat.
    cbn - [arith_wrapper].
    cbn - [list_map2].
    simpl_util.
    unfold list_map2.
    unfold arith_wrapper.
    unfold eval_binop, get_dir, coerce_to.
    unfold arch.dir_beq, ident.internal_nat_beq.

    simpl_util.
    cbn - [arith_wrapper].
    simpl_util.
    unfold seq.cat.
    unfold eval_var; cbn - [eval_node].
    simpl_util; cbn - [eval_node].
    simpl_util; cbn - [eval_node].
    simpl_util; cbn - [eval_node].
    simpl_util; cbn - [eval_node].
    simpl_util; cbn - [eval_node].
    simpl_util; cbn - [eval_node].
    simpl_util; cbn - [eval_node].
    eexists; eexists.
    gen_notation.
    reflexivity.
Qed.

Ltac simpl_util_inner' a :=
    lazymatch a with
    | match ?b with Some _ => _ | None => _ end => simpl_util_inner' b
    | eval_node node_f _ nil None (CoIR _ (?e::nil) _::_) =>
        let v := fresh "v" in
        destruct (node_f_soundness e) as [v ->]
    | eval_node _ node_simeck_box _ None (CoIR _ ?l _::_) =>
        let v1 := fresh "v" in
        let v2 := fresh "v" in
        destruct (node_simeck_box_soundness l) as [v1 [v2 ->]]; [> auto | idtac]
    | _ => let H := fresh "H" in pose (H := a)
    end.

Ltac simpl_util' :=
    lazymatch goal with
    | |- exists v1, ?g = _ /\ _ => simpl_util_inner' g
    end.

Lemma node_ACE_step_soundness:
    forall iL, length iL = 16 ->
        exists l,
        eval_node default_arch node_ACE_step
            ((Id_s simeck_box, eval_node default_arch node_simeck_box ((Id_s syntax.f, eval_node default_arch node_f nil)::nil))
            :: (Id_s syntax.f, eval_node default_arch node_f nil)::nil)
            None (CoIR (DirV 32) iL None::nil) = Some (CoIR (DirV 32) l None::nil)
        /\ length l = 10.
Proof.
    intros iL Hlength.
    do 16 simpl_1 iL Hlength.
    destruct iL; [> clear Hlength | discriminate Hlength].
    unfold eval_node.
    cbn - [eval_node_inner eval_node].
    unfold Pos.to_nat.
    cbn - [eval_node_inner eval_node].
    unfold eval_node_inner.
    cbn - [eval_deq_list eval_node].
    unfold Pos.to_nat; cbn - [eval_node].
    simpl_util'; cbn - [eval_node].
    unfold Pos.to_nat; cbn - [eval_node].
    simpl_util'; cbn - [eval_node].
    simpl_util'; cbn - [eval_node].
    simpl_util'; cbn - [eval_node].
    simpl_util'; cbn - [eval_node].
    eexists; split.
    + reflexivity.
    + auto.
Qed.

Ltac simpl_util_inner'' a :=
    lazymatch a with
    | match ?b with Some _ => _ | None => _ end => simpl_util_inner'' b
    | eval_node node_f _ nil None (CoIR _ (?e::nil) _::_) =>
        let v := fresh "v" in
        destruct (node_f_soundness e) as [v ->]
    | eval_node _ node_simeck_box _ None (CoIR _ ?l _::_) =>
        let v1 := fresh "v" in
        let v2 := fresh "v" in
        destruct (node_simeck_box_soundness l) as [v1 [v2 ->]]; [> auto | idtac]
    | eval_node _ node_ACE_step _ None (CoIR _ ?l _::_) =>
        let v := fresh "l" in
        destruct (node_ACE_step_soundness l) as [v [-> Hlength]];
        [> simpl; reflexivity | idtac];
        do 10 simpl_1 v Hlength; destruct v;
        [> clear Hlength | discriminate Hlength]
    | _ => let H := fresh "H" in pose (H := a)
    end.

Ltac simpl_util2 :=
    lazymatch goal with
    | |- ?g <> None => simpl_util_inner'' g
    end.

Goal
    forall iL, length iL = 10 ->
    eval_node default_arch node_ACE (eval_prog default_arch (node_ACE_step::node_simeck_box::node_f::nil)) None (CoIR (DirV 32) iL None::nil) <> None.
Proof.
    intros iL Hlength;
    do 10 simpl_1 iL Hlength; destruct iL; [> clear Hlength | discriminate Hlength].
    unfold eval_node; cbn - [eval_deq_list eval_node].
    unfold Pos.to_nat; cbn - [eval_deq_list eval_node].
    cbn - [eval_node].
    unfold bind.
    cbn - [eval_node].
    unfold Pos.to_nat; cbn - [eval_node].
    simpl_util2.
    unfold Pos.to_nat; cbn - [eval_node].
    unfold Pos.to_nat; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    simpl_util2; cbn - [eval_node].
    discriminate.
Qed.

