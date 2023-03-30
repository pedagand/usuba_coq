From Usuba Require Import usuba_AST collect usuba_sem equiv_rel utils.
From Coq Require Import FMapAVL.
From Coq Require Import String.
Require Import PeanoNat.
Require Import Ensembles.
Require Import Lia.
Require Import Coq.Structures.OrderedTypeEx.
Require Import List.

(* Module StringOT <: OrderedType.
    Definition t := string.
    Definition eq := @eq t.
    Definition lt : t -> t -> Prop := String_as_OT.lt.
    Definition eq_refl := @refl_equal t.
    Definition eq_sym := @sym_eq t.
    Definition eq_trans := @trans_eq t.
    Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof.
        unfold lt; exact String_as_OT.lt_trans.
    Defined.
    Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y := String_as_OT.lt_not_eq.
    Definition compare : forall x y : t, Compare lt eq x y := String_as_OT.compare.
    Definition eq_dec := string_dec.
End StringOT. *)

Module imap := Make String_as_OT.

Fixpoint get_var_type (env_var : imap.t typ) (v : var) :=
    match v with
    | Var x => imap.find x env_var
    | Index v' _ =>
        match get_var_type env_var v' with
        | Some (Array t _) => Some t
        | Some (Uint dir m n) =>
            if 1 <? n
            then Some (Uint dir m 1)
            else Some (Uint dir (Mint 1) 1)
        | _ => None
        end
    | _ => None
    end.

Definition gen_list_0_int (n : nat) : list nat :=
    let fix aux n acc := match n with
        | 0 => acc
        | S n' => aux n' (n' :: acc) 
    end in aux n nil.

Fixpoint expand_var_inner (typ : typ) (env_it : context) (bitslice : bool) (partial : bool) (v : var) : list var :=
    match typ with
    | Nat => v::nil
    | Uint _ (Mint m) 1 =>
        if 1 <? m
        then
            if bitslice
            then List.map (fun i => Index v (Const_e i)) (gen_list_0_int m)
            else v::nil
        else
            v::nil
    | Uint _ _ 1 | Uint _ _ 0 => v::nil
    | Uint d (Mint m) n =>
        flat_map (fun i => map (fun j => Index (Index v (Const_e i)) (Const_e j)) (gen_list_0_int m)) (gen_list_0_int n)
    | Uint _ _ n =>
        map (fun i => Index v (Const_e i)) (gen_list_0_int n)
    | Array typ s =>
        match eval_arith_expr env_it s with
        | Some len =>
            if partial then
                List.map (fun i => Index v (Const_e i)) (gen_list_0_int len)
            else
                flat_map
                (fun i => expand_var_inner typ env_it bitslice partial (Index v (Const_e i)))
                (gen_list_0_int len)
        | None => nil
        end
    end.

Definition expand_var (env_var : imap.t typ) (env_it : context) (bitslice : bool) (partial : bool) (v : var) : list var :=
    match get_var_type env_var v with
    | None => (v::nil)
    | Some typ => expand_var_inner typ env_it bitslice partial v
    end.

From mathcomp Require Import all_ssreflect.

Lemma map_CoIL_is_lin:
    forall l, linearize_list_value [seq CoIL i | i <- l] nil = [seq CoIL i | i <- l].
Proof.
    move=> l; induction l as [|hd tl HRec]; simpl; trivial.
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

Theorem gen_list_0_int_lemma: 
    forall n, forall l : list nat,
        (fix aux (n : nat) (acc : seq nat) {struct n} : seq nat :=
            match n with
            | 0 => acc
            | n'.+1 => aux n' (n' :: acc)
            end) n l = (fix aux (n : nat) (acc : seq nat) {struct n} : seq nat :=
            match n with
            | 0 => acc
            | n'.+1 => aux n' (n' :: acc)
            end) n nil ++ l.
Proof.
    induction n as [|n HRec]; simpl; trivial.
    move=> l.
    rewrite HRec.
    specialize HRec with [:: n].
    rewrite HRec.
    rewrite <- app_assoc; simpl.
    reflexivity.
Qed.

Theorem gen_list_0_int_S:
    forall n, gen_list_0_int (S n) = gen_list_0_int n ++ n::nil.
Proof.
    unfold gen_list_0_int.
    induction n; simpl; trivial.
    do 2 rewrite (gen_list_0_int_lemma _ (_::_)).
    rewrite <- app_assoc; simpl.
    reflexivity.
Qed.

Fixpoint change_access (i : nat) (acc : access) : access :=
    match acc with
    | AAll => ASlice (i::nil) AAll
    | ASlice iL acc => ASlice iL (change_access i acc)
    end.

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

Theorem length_app {A : Type}:
    forall l1 l2 : list A,
        length (l1 ++ l2) = length l1 + length l2.
Proof.
    move=> l1 l2; induction l1 as [|hd l1 HRec]; simpl.
    {
        rewrite add0n; trivial.
    }
    {
        rewrite addSn.
        rewrite HRec; reflexivity.
    }
Qed.

Theorem length_app_eq {A : Type}:
    forall l1 l2 : list A,
    forall i1 i2,
        length l1 = i1 -> length (l1 ++ l2) = i1 + i2 -> length l2 = i2.
Proof.
    move=> l1 l2; induction l1 as [|hd l1 HRec]; simpl.
    all: move=> i1 i2 <-.
    {
        rewrite add0n; trivial.
    }
    {
        rewrite addSn.
        move=> HEq; inversion HEq.
        refine (HRec _ _ _ _).
        + reflexivity.
        + assumption.
    }
Qed.

Theorem split_into_segments_soundness {A : Type} :
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

Theorem case_last {A : Type}: forall l : list A, {l = nil} + {exists l' last, l = l' ++ last::nil}.
Proof.
    induction l as [|hd tl HRec]; simpl; auto.
    right.
    destruct HRec as [->|[l' [last' ->]]].
    {
        exists nil; exists hd; simpl; reflexivity.
    }
    {
        exists (hd::l'); exists last'; simpl; reflexivity.
    }
Qed.

Theorem Forall_length_1_concat {A : Type}:
    forall l : list (list A),
        Forall (fun l2 => length l2 = 1) l -> length (concat l) = length l.
Proof.
    move=> l; induction l as [|hd l HRec]; simpl; trivial.
    move=> HForall.
    rewrite length_app.
    rewrite HRec.
    + apply Forall_inv in HForall; rewrite HForall; rewrite add1n; reflexivity.
    + apply Forall_inv_tail in HForall; assumption.
Qed.

Theorem split_into_segments_1_r {A : Type}:
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

Theorem take_n_all {A : Type} :
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

Theorem split_into_segments_1_l {A : Type}:
    forall l : list A, forall n,
        length l = n -> split_into_segments 1 n l = Some [:: l].
Proof.
    simpl.
    move=> l n length_eq.
    rewrite take_n_all; trivial.
Qed.

Theorem get_access_split_lemma:
    forall n iL l_tl form_tl,
        Forall (fun l => length l = prod_list form_tl) (iL ++ l_tl) ->
        length iL = n ->
        prod_list form_tl = 1 ->
        Some (concat (iL ++ l_tl)) =
        fold_right (fun i l =>
            l' <- l;
            v <- get_access (concat (iL ++ l_tl)) (ASlice [:: i] AAll) (length (concat (iL ++ l_tl))::form_tl); Some (v ++ l')) (Some (concat l_tl)) (gen_list_0_int n).
Proof.
    move=> n; induction n as [|n HRec].
    {
        move=> iL l_tl tl.
        destruct iL as [|hd iL]; simpl; trivial.
        discriminate.
    }
    move=> iL l_tl tl HForall Hlength prod_eq_1.
    rewrite gen_list_0_int_S.
    rewrite fold_right_app.
    destruct (case_last iL) as [HEq|[iL_front [iL_last HEq]]].
    {
        rewrite HEq; rewrite HEq in Hlength.
        clear HForall HEq iL.
        simpl in Hlength; discriminate.
    }
    rewrite HEq; rewrite HEq in Hlength; rewrite HEq in HForall.
    repeat rewrite concat_app.
    repeat rewrite <- app_assoc.
    do 2 rewrite <- concat_app.
    rewrite (HRec iL_front (iL_last :: l_tl) tl); clear HRec.
    {
        f_equal.
        rewrite length_app in Hlength.
        simpl in Hlength.
        rewrite addn1 in Hlength; injection Hlength; clear Hlength; move=> Hlength.
        rewrite prod_eq_1 in HForall.
        rewrite Forall_app in HForall.
        destruct HForall as [HForall_front HForall_tl].
        rewrite Forall_app in HForall_front.
        destruct HForall_front as [HForall_front HForall_last].
        apply Forall_inv in HForall_last.
        destruct iL_last; simpl in HForall_last.
        by discriminate.
        destruct iL_last; simpl in HForall_last.
        2: by discriminate.
        clear HForall_last.
        simpl.
        destruct tl.
        {
            rewrite concat_app; simpl.
            clear prod_eq_1.
            rewrite length_app; simpl.
            simpl in *.
            repeat rewrite Forall_length_1_concat.
            2-3: by assumption.
            rewrite Nat.mod_same.
            2: by rewrite addnS; auto.
            rewrite Nat.eqb_refl.
            rewrite Nat.div_same.
            2: by rewrite addnS; auto.
            rewrite split_into_segments_1_r.
            2: by rewrite length_app; simpl; repeat rewrite Forall_length_1_concat; auto.
            rewrite nth_error_map.
            rewrite nth_error_app2; rewrite Forall_length_1_concat; trivial; rewrite Hlength.
            2: lia.
            rewrite Nat.sub_diag; simpl; reflexivity.
        }
        rewrite Nat.mod_same.
        2: by rewrite concat_app; rewrite length_app; simpl; rewrite addnS; auto.
        rewrite Nat.eqb_refl.
        rewrite Nat.div_same.
        2: by rewrite concat_app; rewrite length_app; simpl; rewrite addnS; auto.
        rewrite split_into_segments_1_r.
        2: by reflexivity.
        rewrite nth_error_map.
        rewrite concat_app.
        rewrite nth_error_app2; rewrite Forall_length_1_concat; trivial. rewrite Hlength.
        2: lia.
        rewrite Nat.sub_diag; simpl.
        simpl in prod_eq_1.
        destruct n1 as [|n1].
        by rewrite mul0n in prod_eq_1; discriminate.
        destruct n1 as [|n1].
        by rewrite Nat.mod_same; auto.
        destruct (prod_list tl).
        by rewrite muln0 in prod_eq_1; discriminate.
        do 2 rewrite mulSn in prod_eq_1.
        do 2 rewrite addSn in prod_eq_1.
        rewrite addnS in prod_eq_1.
        discriminate.
    }
    {
        rewrite <- app_assoc in HForall.
        simpl in HForall.
        assumption.
    }
    {
        rewrite length_app in Hlength; simpl in Hlength.
        rewrite addn1 in Hlength; injection Hlength.
        auto.
    }
    {
        assumption.
    }
Qed.

Inductive well_bounded : access -> list nat -> nat -> Prop :=
    | wb_Bot : forall n, well_bounded AAll (n::nil) n
    | wb_Ind : forall acc form n, well_bounded acc form n ->
        well_bounded (ASlice (0::nil) acc) (1::form) n.

Theorem get_access_split:
    forall form acc n,
        well_bounded acc form n ->
    forall iL,
        length iL = n ->
        n <> 0 ->
        get_access iL acc form =
        fold_right (fun i l =>
            l' <- l; v <- get_access iL (change_access i acc) form; Some (v ++ l')) (Some nil) (gen_list_0_int n).
Proof.
    move=> form acc n Hwb; induction Hwb as [n|acc form n wb HRec].
    {
        move=> iL length_eq not_zero.
        pose (p := get_access_split_lemma n (map (fun i => [:: i]) iL) nil nil); move:p.
        rewrite cats0.
        assert (concat (map (fun i => [:: i]) iL) = iL) as HEq.
        {
            clear.
            induction iL as [|hd tl HRec]; simpl; auto.
            f_equal; assumption.
        }
        rewrite HEq; clear HEq.
        rewrite map_length; rewrite length_eq.
        rewrite concat_nil.
        move=> <-; simpl; trivial.
        {
            rewrite length_eq.
            rewrite Nat.mod_same; trivial; simpl.
            rewrite Nat.div_same; trivial.
            rewrite split_into_segments_1_r; trivial.
        }
        rewrite Forall_map; simpl.
        clear; induction iL; constructor; trivial.
    }
    {
        unfold change_access; fold change_access.
        move=> iL length_eq not_zero.
        unfold get_access; fold get_access.
        rewrite Nat.mod_1_r; rewrite Nat.eqb_refl.
        rewrite Nat.div_1_r.
        rewrite split_into_segments_1_l; trivial.
        simpl.
        rewrite HRec; trivial.
        match goal with
        | |- match fold_right ?f1 _ _ with Some _ => _ | None => None end
            = fold_right ?f2 _ _ =>
                assert (forall l, fold_right f1 (Some nil) l = fold_right f2 (Some nil) l) as HEq;
                [> idtac | rewrite HEq; destruct (fold_right f2 (Some nil) (gen_list_0_int n)); trivial]
        end.
        2: by rewrite cats0; reflexivity.
        clear.
        move=> l; induction l as [|hd tl HRec]; simpl; trivial.
        rewrite HRec; clear.
        match goal with
        | |- match ?e with Some _ => _ | None => None end = _ => case e end; trivial.
        move=> l.
        destruct (get_access iL (change_access hd acc) form); trivial.
        rewrite cats0; reflexivity.
    }
Qed.

Theorem linearize_map_CoIL: forall l1 l2, linearize_list_value (map CoIL l1) l2 = (map CoIL l1) ++ l2.
Proof.
    move=> l1 l2; induction l1 as [|hd l1 HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Theorem list_map_seq_map {A B : Type} (f : A -> B):
    forall l, List.map f l = [seq f i | i <- l].
Proof.
    move=> l; induction l as [|hd tl HRec]; simpl; trivial.
Qed.

Fixpoint unfold_access (acc : access) (v : var) : var :=
    match acc with
    | AAll => v
    | ASlice (i::nil) acc_tl => unfold_access acc_tl (Index v (Const_e i))
    | ASlice l acc_tl => unfold_access acc_tl (Slice v (map Const_e l))
    end.

Inductive var_equiv : var -> var -> Prop :=
    | VEBot : forall i, var_equiv (Var i) (Var i)
    | VEInd : forall v1 v2 ae1 ae2, var_equiv v1 v2 -> var_equiv (Index v1 ae1) (Index v2 ae2)
    | VESlice : forall v1 v2 l1 l2, var_equiv v1 v2 -> var_equiv (Slice v1 l1) (Slice v2 l2)
    | VERange : forall v1 v2 i1 i1b i2 i2b, var_equiv v1 v2 -> var_equiv (Range v1 i1 i1b) (Range v2 i2 i2b).

Lemma var_equiv_refl:
    forall v, var_equiv v v.
Proof.
    move=> v; induction v; constructor; assumption.
Qed.

#[global]
Add Relation var var_equiv
    reflexivity proved by var_equiv_refl as var_equiv_def.

Lemma unfold_access_var_equiv:
    forall acc v1 v2,
        var_equiv v1 v2 -> var_equiv (unfold_access acc v1) (unfold_access acc v2).
Proof.
    move=> acc; induction acc as [|iL acc HRec]; simpl; trivial.
    {
        move=> v1 v2 v_equiv.
        destruct iL as [|hd iL]; simpl.
        {
            apply HRec; constructor; assumption.
        }
        destruct iL; apply HRec; constructor; assumption.
    }
Qed.

Lemma get_type_var_equiv:
    forall type_ctxt v1 v2,
        var_equiv v1 v2 -> get_var_type type_ctxt v1 = get_var_type type_ctxt v2.
Proof.
    move=> type_ctxt v1 v2 ve; induction ve as [i|v1 v2 ae1 ae2 ve HRec| |].
    all: simpl; trivial.
    {
        rewrite HRec; reflexivity.
    }
Qed.

Theorem expand_var_lemma:
    forall v acc type_ctxt ctxt d m n,
        get_var_type type_ctxt (unfold_access acc v) = Some (Uint d m n) ->
        well_typed_ctxt (imap.elements type_ctxt) ctxt ->
        n <> 0 ->
        eval_var ctxt v acc =
        fold_right (fun i l =>
            l' <- l;
            v' <- eval_var ctxt v (change_access i acc);
            Some (linearize_list_value v' l')) (Some nil) (gen_list_0_int n).
Proof.
    move=> v; induction v as [i|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl.
    {
        move=> acc type_ctxt ctxt d m n Hfind well_typed.
        case_eq (find_val ctxt i).
        {
            move=> c Hfind_val.
            apply (well_typed_ctxt_imp_find_val _ _ i c) in well_typed; trivial.
            destruct well_typed as [typ [Hfind_type valoType]].
            assert (Uint d m n = typ) as HEq by admit.
            destruct HEq.
            destruct c as [cst|dir iL o]; simpl in *.
            {
                destruct m; simpl in *.
                2-3: destruct valoType.
                destruct valoType as [_ [HEq1 HEq2]].
                symmetry in HEq1; destruct HEq1.
                symmetry in HEq2; destruct HEq2.
                simpl.
                clear.
                move=> _.
                induction acc as [|iL acc HRec]; simpl; trivial.
                case (forallb (Nat.eqb^~ 0) iL); trivial.
                destruct (get_access [:: cst] acc nil) as [v1|].
                all: destruct (get_access [:: cst] (change_access 0 acc) nil) as [v2|]; trivial.
                2,3: by discriminate.
                rewrite linearize_map_CoIL in HRec.
                rewrite linearize_map_CoIL.
                rewrite cats0.
                rewrite cats0 in HRec.
                assert (v1 = v2) as HEq.
                2: by destruct HEq; reflexivity.
                inversion HRec as [HEq]; move: HEq; clear.
                move: v2; induction v1 as [|hd tl HRec].
                all: move=> [|hd2 tl2]; simpl.
                by reflexivity.
                by discriminate.
                by discriminate.
                move=> HEq.
                inversion HEq.
                f_equal; apply HRec; assumption.
            }
            {
                destruct m; simpl in *.
                2-3: by destruct valoType.
                destruct o; simpl in *.
                2: by destruct valoType.
                destruct valoType as [simpl_form [Hlength HDir]].
                move=> NotZero.
                rewrite muln1 in Hlength.
                rewrite (get_access_split _ _ n); trivial.
                2: admit.
                case_eq (gen_list_0_int n).
                {
                    destruct n as [|n]; simpl.
                    + exfalso; apply NotZero; reflexivity.
                    + rewrite gen_list_0_int_S.
                        destruct (gen_list_0_int n); simpl; discriminate.
                }
                clear.
                move=> hd tl _.
                pose (L := hd :: tl); fold L. 
                assert (L <> nil) as NotEmpty by (unfold L; discriminate).
                move: L NotEmpty; clear; move=> L; induction L as [|hd tl HRec]; simpl.
                by move=> Err; exfalso; apply Err; reflexivity.
                move=> _.
                case_eq (length tl =? 0).
                {
                    rewrite Nat.eqb_eq; destruct tl; simpl.
                    2: discriminate.
                    destruct (get_access iL (change_access hd acc) l) as [x|]; trivial.
                    simpl; rewrite cats0; reflexivity.
                }
                move=> l_not_Zero.
                rewrite <- HRec; clear HRec.
                all: swap 1 2.
                {
                    move=> HEq; rewrite HEq in l_not_Zero.
                    simpl in l_not_Zero.
                    discriminate.
                }
                match goal with
                | |- match match ?f with Some _ => _ | None => _ end with Some _ => _ | None => _ end = _ => pose (p := f); fold p
                end.
                destruct p; trivial.
                destruct (get_access iL (change_access hd acc) l); trivial.
                simpl.
                rewrite internal_dir_dec_lb0; trivial.
            }
        }
        {
            destruct n.
            {
                move=> _ NotZero; exfalso; apply NotZero; reflexivity.
            }
            rewrite gen_list_0_int_S; rewrite fold_right_app; simpl.
            move=> _ _; clear.
            induction (gen_list_0_int n) as [|hd tl HRec]; simpl; trivial.
            rewrite <- HRec; reflexivity.
        }
    }
    {
        move=> acc type_ctxt ctxt d m n.
        case (eval_arith_expr ctxt ae).
        all: swap 1 2.
        {
            move=> _ _ NotZero.
            destruct n.
            by exfalso; apply NotZero; reflexivity.
            rewrite gen_list_0_int_S; rewrite fold_right_app; simpl.
            clear; induction (gen_list_0_int n) as [|hd tl HRec]; simpl; trivial.
            rewrite <- HRec; reflexivity.
        }
        move=> i get_type well_typed not_zero.
        specialize HRec with (ASlice [:: i] acc) type_ctxt ctxt d m n.
        simpl in HRec.
        rewrite <- HRec; trivial.
        rewrite <- get_type.
        apply get_type_var_equiv.
        apply unfold_access_var_equiv.
        constructor.
        reflexivity.
    }
    {
        move=> acc type_ctxt ctxt d m n get_type.
        exfalso.
        admit.
    }
    {
        move=> acc type_ctxt ctxt d m n get_type.
        exfalso.
        admit.
    }
Admitted.

Theorem expand_var_inner_soundness:
    forall type_ctxt typ env_it partial v,
        get_var_type type_ctxt v = Some typ ->
        (forall n, Ensembles.In ident (typ_freevars typ) n -> exists c, find_const env_it n = Some c) ->
            eval_var env_it v AAll
            = fold_right
                (fun v l=> l' <- l; v' <- eval_var env_it v AAll; Some (linearize_list_value v' l'))
                (Some nil) (expand_var_inner typ env_it false partial v).
Proof.
    move=> type_ctxt typ env_it partial.
    induction typ as [|d [] [|n]|]; simpl.
    1-2,4,6: move=> v _ _.
    1-4: pose (p := eval_var_linearize_fixpoint env_it v AAll); move: p.
    1-4: destruct (eval_var env_it v AAll) as [l|]; trivial.
    1-4: move=> HEq; specialize HEq with l; move: HEq.
    1-4: impl_tac; trivial.
    1-4: move=> ->; reflexivity.
    {
        destruct n as [|n]; simpl.
        {
            case_eq (1 <? n0); simpl.
            all: swap 1 2.
            {
                intros; pose (p := eval_var_linearize_fixpoint env_it v AAll); move: p.
                clear.
                case (eval_var env_it v AAll); trivial.
                move=> l H; specialize H with l; move: H.
                impl_tac; [> by reflexivity | idtac ].
                move=> ->; reflexivity.
            }
            {
                intros; pose (p := eval_var_linearize_fixpoint env_it v AAll); move: p.
                clear.
                case (eval_var env_it v AAll); trivial.
                move=> l H; specialize H with l; move: H.
                impl_tac; [> by reflexivity | idtac ].
                move=> ->; reflexivity.
            }
        }
        move=> v get_type _.
        (* rewrite (expand_var_lemma . *)
        do 2 rewrite gen_list_0_int_S; simpl.
        rewrite <- app_assoc; simpl.
        rewrite flat_map_app; simpl.
        admit.
    }
    all: admit.
Admitted.