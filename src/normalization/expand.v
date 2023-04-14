From Usuba Require Import 
    ident usuba_AST usuba_ASTProp arch collect usuba_sem usuba_semProp equiv_rel utils
    coq_missing_lemmas.
Require Import Lia.
Require Import OrderedType.
Require Import ZArith.
From mathcomp Require Import ssrnat seq.

Fixpoint get_var_type (env_var : imap.t typ) (v : var) :=
    match v with
    | Var x => imap.find x env_var
    | Index v' _ =>
        match get_var_type env_var v' with
        | Some (Array t _) => Some t
        | Some (Uint dir m n) =>
            Some (Uint dir m 1)
        | _ => None
        end
    | _ => None
    end.

Definition gen_list_0_int (n : nat) : list nat :=
    let fix aux n acc := match n with
        | 0 => acc
        | S n' => aux n' (n' :: acc) 
    end in aux n nil.

Fixpoint expand_var_inner (typ : typ) (env_it : context) (partial : bool) (v : var) : list var :=
    match typ with
    | Nat => v::nil
    | Uint _ _ 1 => v::nil
    | Uint _ _ n =>
        map (fun i => Index v (Const_e (Z.of_nat i))) (gen_list_0_int n)
    | Array typ s =>
        match eval_arith_expr env_it s with
        | Some len =>
            if partial then
                List.map (fun i => Index v (Const_e (Z.of_nat i))) (gen_list_0_int len)
            else
                flat_map
                (fun i => expand_var_inner typ env_it partial (Index v (Const_e (Z.of_nat i))))
                (gen_list_0_int len)
        | None => nil
        end
    end.

Definition expand_var (env_var : imap.t typ) (env_it : context) (partial : bool) (v : var) : list var :=
    match get_var_type env_var v with
    | None => (v::nil)
    | Some typ => expand_var_inner typ env_it partial v
    end.

From mathcomp Require Import all_ssreflect.

Fixpoint expand_access (acc : access) : list access :=
    match acc with
    | AAll => [:: AAll]
    | ASlice nil tl => map (ASlice nil) (expand_access tl)
    | ASlice (i::nil) tl => map (ASlice [:: i]) (expand_access tl)
    | ASlice iL tl =>
        flat_map (fun i => map (ASlice [:: i]) (expand_access tl)) iL 
    end.

Theorem expand_access_not_empty:
    forall acc, expand_access acc <> nil.
Proof.
    move=> acc; induction acc as [|iL acc HRec]; simpl.
    by discriminate.
    destruct iL as [|i []]; destruct expand_access; simpl.
    all: by idtac.
Qed.

Theorem remove_option_from_list_None {A : Type}:
    forall l, In None l -> @remove_option_from_list A l = None.
Proof.
    move=> l; induction l as [|hd tl HRec]; move=> HIn.
    {
        inversion HIn.
    }
    {
        inversion HIn as [H|H].
        by rewrite H; auto.
        destruct hd; simpl; trivial.
        rewrite HRec; trivial.
    }
Qed.

Theorem remove_option_from_list_app {A : Type}:
    forall l1 l2, In None l2 -> @remove_option_from_list A (l1 ++ l2) = None.
Proof.
    move=> l1 l2 HIn; induction l1 as [|[] tl HRec]; simpl; trivial.
    + apply remove_option_from_list_None; trivial.
    + rewrite HRec; reflexivity.
Qed.

Theorem remove_option_from_list_app2 {A : Type}:
    forall l1 l2, remove_option_from_list l1 = None -> @remove_option_from_list A (l1 ++ l2) = None.
Proof.
    move=> l1 l2 HIn; induction l1 as [|[] tl HRec]; simpl in *; trivial.
    + discriminate.
    + rewrite HRec; trivial; destruct remove_option_from_list; by idtac.
Qed.

Theorem remove_option_from_list_app3 {A : Type}:
    forall l1 l2, remove_option_from_list l2 = None -> @remove_option_from_list A (l1 ++ l2) = None.
Proof.
    move=> l1 l2 HIn; induction l1 as [|[] tl HRec]; simpl in *; trivial.
    + rewrite HRec; trivial; destruct remove_option_from_list; by idtac.
Qed.

Lemma remove_option_from_list_lemma {A : Type}:
    forall (l1 : list A) l2 l3 l4,
        Some l1 = omap flatten (remove_option_from_list l2) ->
        Some l3 = omap flatten (remove_option_from_list l4) ->
        Some (l1 ++ l3) = omap flatten (remove_option_from_list (l2 ++ l4)).
Proof.
    move=> l1 l2 l3 l4; move: l1; induction l2 as [|hd tl HRec]; simpl.
    {
        move=> l1 H1 H2.
        inversion H1; auto.
    }
    {
        move=> l1 H1 H2.
        destruct hd as [hd|]; simpl in *.
        2: discriminate.
        destruct (remove_option_from_list tl); simpl in *.
        2: discriminate.
        inversion H1.
        pose (p := HRec (flatten l)); move: p.
        do 2 (impl_tac; auto).
        clear.
        destruct remove_option_from_list; simpl.
        2: discriminate.
        move=> H; inversion H.
        rewrite catA; reflexivity.
    }
Qed.

Theorem get_access_expand_access:
    forall acc form vL,
        get_access vL acc form =
        omap flatten
        (remove_option_from_list
            (map (fun acc' => get_access vL acc' form)
                (expand_access acc))).
Proof.
    intro acc; induction acc as [|iL acc HRec]; simpl.
    all: intros [|form_hd form_tl] vL.
    {
        destruct vL as [|[] []]; auto.
    }
    {
        destruct (length _ mod _ =? _); auto.
        destruct split_into_segments; auto.
        destruct remove_option_from_list; auto.
        simpl; rewrite cats0; reflexivity.
    }
    {
        destruct iL as [|h []]; simpl.
        {
            rewrite <-map_comp.
            unfold comp.
            simpl.
            destruct vL as [|h []].
            {
                pose (p := expand_access_not_empty acc); move: p; move=> p.
                destruct expand_access; simpl; by idtac.
            }
            {
                rewrite HRec.
                clear; induction (expand_access acc) as [|hd tl HRec]; simpl; trivial.
                destruct get_access; auto.
                destruct remove_option_from_list; simpl in *.
                all: destruct remove_option_from_list; simpl in *; auto.
            }
            {
                pose (p := expand_access_not_empty acc); move: p; move=> p.
                destruct expand_access; simpl; by idtac.
            }
        }
        {
            rewrite <-map_comp; unfold comp; simpl.
            destruct (h =? 0); clear h; simpl.
            {
                destruct vL as [|h []].
                {
                    pose (p := expand_access_not_empty acc); move: p; move=> p.
                    destruct expand_access; simpl; by idtac.
                }
                {
                    rewrite HRec.
                    clear; induction (expand_access acc) as [|hd tl HRec]; simpl; trivial.
                    destruct get_access; auto.
                    destruct remove_option_from_list; simpl in *.
                    all: destruct remove_option_from_list; simpl in *; auto.
                    2-3: discriminate.
                    do 2 rewrite app_nil_r; rewrite app_nil_r in HRec.
                    inversion HRec; reflexivity.
                }
                {
                    pose (p := expand_access_not_empty acc); move: p; move=> p.
                    destruct expand_access; simpl; by idtac.
                }
            }
            {
                pose (p := expand_access_not_empty acc); move: p; move=> p.
                destruct expand_access; simpl.
                by idtac.
                destruct vL as [|i []]; auto.
            }
        }
        destruct vL as [|h' []].
        {
            pose (p := expand_access_not_empty acc); move: p; move=> p.
            destruct expand_access; simpl; trivial.
            by idtac.
        }
        all: swap 1 2.
        {
            pose (p := expand_access_not_empty acc); move: p; move=> p.
            destruct expand_access; simpl; trivial.
            by idtac.
        }
        {
            do 2 rewrite map_cat.
            do 2 rewrite <- map_comp; unfold comp; simpl.
            destruct h; simpl.
            2: pose (p := expand_access_not_empty acc); move: p; move=> p.
            2: destruct expand_access; simpl; trivial.
            2: by idtac.
            destruct n; simpl.
            2: rewrite remove_option_from_list_app; auto.
            2: pose (p := expand_access_not_empty acc); move: p; move=> p.
            2: destruct expand_access; simpl; auto.
            2: by idtac.
            pose (p := HRec nil [:: h']); move: p; move=> p.
            assert ([seq match get_access [:: h'] x [::] with
                    | Some l0 => Some (l0 ++ [::])%list
                    | None => None end | x <- expand_access acc]
                    = [seq get_access [:: h'] acc' [::] | acc' <- expand_access acc]) as HEq.
            {
                clear.
                induction expand_access as [|h tl HRec]; simpl; trivial.
                destruct get_access; f_equal; auto.
                rewrite app_nil_r; reflexivity.
            }
            rewrite HEq; clear HRec.
            destruct get_access.
            all: swap 1 2.
            {
               rewrite remove_option_from_list_app2.
               + by destruct forallb.
               + by destruct remove_option_from_list.
            }
            case_eq (forallb (Nat.eqb^~ 0) l).
            all: swap 1 2.
            {
                rewrite <- Bool.not_true_iff_false; rewrite forallb_forall.
                clear; move=> HForall.
                rewrite remove_option_from_list_app3; auto.
                rewrite remove_option_from_list_app3; auto.
                induction l as [|hd tl HRec].
                {
                    exfalso; apply HForall; clear.
                    move=> x HIn; inversion HIn.
                }
                simpl; rewrite map_cat.
                destruct hd; simpl.
                {
                    apply remove_option_from_list_app3.
                    apply HRec.
                    move=> HImp; apply HForall; move=> elt HIn.
                    inversion HIn as [H|H].
                    + rewrite <- H; auto.
                    + auto.
                }
                {
                    apply remove_option_from_list_app2.
                    rewrite <- map_comp; unfold comp; simpl.
                    pose (p := expand_access_not_empty acc); move: p.
                    destruct expand_access; simpl; auto.
                    by idtac.
                }
            }
            rewrite forallb_forall; move=> Hforall.
            apply remove_option_from_list_lemma; trivial.
            apply remove_option_from_list_lemma; trivial.
            induction l as [|hd tl HRec]; simpl; trivial.
            rewrite map_cat; rewrite <- map_comp; unfold comp.
            apply remove_option_from_list_lemma; trivial.
            {
                specialize Hforall with hd.
                move: Hforall; impl_tac.
                by constructor.
                rewrite Nat.eqb_eq.
                move=> ->; clear hd; simpl.
                rewrite HEq; trivial.
            }
            {
                apply HRec.
                move=> elt HIn; apply Hforall.
                constructor 2; assumption.
            }
        }
    }
    {
        destruct iL as [|i1 [|i2 tl]]; simpl.
        {
            rewrite <- map_comp; unfold comp; simpl.
            destruct (_ =? _).
            {
                destruct split_into_segments; clear.
                + induction expand_access as [|hd tl HRec]; simpl; trivial.
                    destruct remove_option_from_list; simpl in *.
                    - inversion HRec; reflexivity.
                    - discriminate.
                + pose (p := expand_access_not_empty acc); move: p.
                    destruct expand_access; by simpl.
            }
            {
                pose (p := expand_access_not_empty acc); move: p.
                destruct expand_access; by simpl.
            }
        }
        {
            rewrite <- map_comp; unfold comp; simpl.
            destruct (_ =? _).
            2: pose (p := expand_access_not_empty acc); move: p.
            2: destruct expand_access; by simpl.
            destruct split_into_segments.
            2: pose (p := expand_access_not_empty acc); move: p.
            2: destruct expand_access; by simpl.
            destruct nth_error.
            2: pose (p := expand_access_not_empty acc); move: p.
            2: destruct expand_access; by simpl.
            rewrite HRec.
            match goal with
            | |- match ?a with Some _ => _ | None => _ end = ?b =>
                assert (a = b) as HEq; [> f_equal | rewrite HEq; destruct b; auto; rewrite cats0; reflexivity]
            end.
            f_equal.
            clear.
            induction expand_access as [|hd tl HRec]; simpl; trivial.
            rewrite <- HRec.
            destruct get_access; auto.
            rewrite cats0; reflexivity.
        }
        {
            do 2 rewrite map_cat; do 2 rewrite <- map_comp; unfold comp; simpl.
            case_eq (length vL mod form_hd =? 0).
            2: pose (p := expand_access_not_empty acc); move: p.
            2: destruct expand_access; by simpl.
            move=> mod_Eq.
            case_eq (split_into_segments form_hd (length vL / form_hd) vL).
            2: pose (p := expand_access_not_empty acc); move: p.
            2: destruct expand_access; by simpl.
            move=> vL' split_Eq.
            destruct (nth_error _ i1) as [l1|].
            2: pose (p := expand_access_not_empty acc); move: p.
            2: destruct expand_access; [> by idtac | simpl].
            2: destruct fold_right; trivial; destruct nth_error; trivial.
            2: destruct get_access; trivial.
            destruct nth_error as [l2|].
            all: swap 1 2.
            {
                rewrite remove_option_from_list_app3.
                2: apply remove_option_from_list_app2.
                2: pose (p := expand_access_not_empty acc); move: p.
                2: destruct expand_access; by simpl.
                destruct fold_right; simpl; trivial.
            }
            assert (forall l, [seq match get_access l x form_tl with
                | Some l0 => Some (l0 ++ [::])
                | None => None end | x <- expand_access acc]
                = [seq get_access l acc' form_tl | acc' <- expand_access acc]) as HEq.
            {
                clear; move=> l.
                induction expand_access as [|h tl HRec]; simpl; trivial.
                destruct get_access; f_equal; auto.
                rewrite cats0; reflexivity.
            }
            do 2 rewrite HEq.
            rewrite (HRec _ l1).
            case_eq (remove_option_from_list [seq get_access l1 acc' form_tl | acc' <- expand_access acc]).
            all: swap 1 2.
            {
                simpl; intro.
                rewrite remove_option_from_list_app2; trivial.
                destruct fold_right; auto.
                destruct get_access; auto.
            }
            move=> l1' HEq_l1.
            rewrite (HRec _ l2).
            case_eq (remove_option_from_list [seq get_access l2 acc' form_tl | acc' <- expand_access acc]).
            all: swap 1 2.
            {
                simpl; intro.
                rewrite remove_option_from_list_app3.
                2: rewrite remove_option_from_list_app2; trivial.
                destruct fold_right; auto.
            }
            move=> l2' HEq_l2; simpl.
            match goal with
            | |- match match ?f with Some _ => _ | None => _ end with Some _ => _ | None => _ end
                = omap flatten (remove_option_from_list (_ ++ _ ++ ?l)) =>
                    assert (f = omap flatten (remove_option_from_list l)) as HEq';
                    [> idtac | rewrite HEq'; clear HEq'; case_eq (omap flatten (remove_option_from_list l))]
            end.
            all: swap 1 2.
            {
                move=> l3 HEq_l3.
                apply remove_option_from_list_lemma.
                by rewrite HEq_l1; auto.
                apply remove_option_from_list_lemma.
                by rewrite HEq_l2; auto.
                by symmetry; assumption.
            }
            all: swap 1 2.
            {
                move=> HEq_l3.
                rewrite remove_option_from_list_app3; auto.
                rewrite remove_option_from_list_app3; auto.
                match goal with | |- ?l = _ => destruct l end; trivial.
                discriminate.
            }
            move: (HRec form_tl) split_Eq mod_Eq HEq; clear; move=> HRec split_Eq mod_Eq HEq.
            induction tl as [|hd tl HRec']; simpl; trivial.
            rewrite HRec'; clear HRec'.
            rewrite map_cat; rewrite <- map_comp; unfold comp; simpl.
            rewrite mod_Eq; rewrite split_Eq.
            destruct nth_error; swap 1 2.
            {
                rewrite remove_option_from_list_app2.
                + simpl; destruct omap; reflexivity.
                + clear; move: (expand_access_not_empty acc); by destruct expand_access.
            }
            rewrite HRec.
            rewrite HEq.
            case_eq (remove_option_from_list [seq get_access l acc' form_tl | acc' <- expand_access acc]); simpl.
            all: swap 1 2.
            {
                intro.
                rewrite remove_option_from_list_app2; trivial; simpl.
                destruct omap; reflexivity.
            }
            move=> l_top HEq1.
            match goal with |- _ = omap flatten (remove_option_from_list (_ ++ ?l)) => case_eq (remove_option_from_list l) end.
            2: by intro; rewrite remove_option_from_list_app3; trivial.
            simpl.
            intros l_tail HEq2.
            apply remove_option_from_list_lemma.
            + rewrite HEq1; auto.
            + rewrite HEq2; auto.
        }
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

Theorem get_access_split_lemma:
    forall n : nat, forall iL l_tl : list (list (option Z)),
    forall form_tl,
        Forall (fun l => length l = prod_list form_tl) (iL ++ l_tl) ->
        length iL = n ->
        prod_list form_tl = 1 ->
        remove_option_from_list (concat (iL ++ l_tl)) =
        fold_right (fun i l =>
            l' <- l;
            v <- get_access (concat (iL ++ l_tl))
                    (ASlice [:: i] AAll)
                    (length (concat (iL ++ l_tl))::form_tl);
                    (Some (v ++ l')))
                    (remove_option_from_list (concat l_tl))
                (gen_list_0_int n).
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
        destruct iL_last as [|h1 iL_last]; simpl in HForall_last.
        by discriminate.
        destruct iL_last; simpl in HForall_last.
        2: by discriminate.
        clear HForall_last.
        simpl.
        destruct tl as [|n1 tl].
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
            rewrite Nat.sub_diag; simpl.
            destruct (remove_option_from_list (concat l_tl)).
            all: destruct h1; trivial.
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
        destruct (remove_option_from_list (concat l_tl)).
        2: by destruct h1; reflexivity.
        destruct n1 as [|n1].
        by rewrite mul0n in prod_eq_1; discriminate.
        destruct n1 as [|n1].
        {
            rewrite Nat.mod_same; simpl; auto.
            destruct h1; simpl; reflexivity.
        }
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
    | wb_Bot : forall n l, Forall (eq 1) l -> well_bounded AAll (n::l) n
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
        unfold remove_option_from_list; fold (@remove_option_from_list nat).
        impl_tac.
        {
            rewrite Forall_map.
            clear; induction iL; constructor; simpl in *; trivial.
        }
        impl_tac; trivial.
        impl_tac.
        by simpl; reflexivity.
        unfold change_access.
        admit.
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
Admitted.

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

Fixpoint not_all_ind (acc : var) : bool :=
    match acc with
    | Var v => false
    | Index v _ => not_all_ind v
    | Slice _ _ | Range _ _ _ => true
    end.

Lemma not_all_ind_imp_get_var_type_is_None:
    forall v, not_all_ind v = true -> forall type_ctxt, get_var_type type_ctxt v = None.
Proof.
    move=> v; induction v as [v|v HRec ae| |]; simpl; trivial.
    by discriminate.
    intros; rewrite HRec; auto.
Qed.

Lemma unfold_access_not_all_ind:
    forall acc v, not_all_ind v = true -> not_all_ind (unfold_access acc v) = true.
Proof.
    move=> acc; induction acc as [|iL acc HRec]; simpl; auto.
    move=> v H.
    destruct iL as [|hd tl].
    {
        apply HRec; simpl; reflexivity.
    }
    destruct tl; apply HRec; simpl; trivial.
Qed.

Lemma get_var_index:
    forall type_ctxt acc v d m d' m' n',
        get_var_type type_ctxt v = Some (Uint d m 1) ->
        get_var_type type_ctxt (unfold_access acc v) = Some (Uint d' m' n') ->
        d' = d /\ m' = m /\ n' = 1.
Proof.
    move=> type_ctxt acc.
    induction acc as [|[|hd []] acc HRec]; simpl.
    {
        move=> v d m d' m' n' -> H; inversion H.
        auto.
    }
    {
        do 7 intro.
        rewrite not_all_ind_imp_get_var_type_is_None.
        by discriminate.
        apply unfold_access_not_all_ind; auto.
    }
    {
        do 6 intro; move=> H.
        apply HRec; trivial.
        simpl.
        rewrite H; reflexivity.
    }
    {
        do 7 intro.
        rewrite not_all_ind_imp_get_var_type_is_None.
        by discriminate.
        apply unfold_access_not_all_ind; auto.
    }
Qed.

(*Lemma get_var_type_well_bounded:
    forall (type_ctxt : imap.t typ) acc v d m n,
        1 < n ->
        get_var_type type_ctxt (unfold_access acc v) = Some (Uint d (Mint m) n) ->
        get_var_type type_ctxt v = Some (Uint d (Mint m) n) ->
        acc = AAll.
Proof.
    move=> type_ctxt acc v d m n sup.
    move: v.
    induction acc as [|iL acc HRec]; trivial; simpl.
    move=> v.
    simpl; destruct iL as [|hd []]; simpl.
    1,3: rewrite not_all_ind_imp_get_var_type_is_None.
    1,3: by discriminate.
    1-2: apply unfold_access_not_all_ind; auto.
    move=> H1 H2.
    specialize HRec with (Index v (Const_e hd)); move: HRec.
    impl_tac; trivial.
    impl_tac; trivial.
    destruct acc as [|iL' acc]; move=> get_type; simpl in *.
    {
        destruct iL as [|hd iL]; simpl in *.
        by discriminate.
        destruct iL; simpl in *.
        2: by discriminate.
        rewrite HFind in get_type.
        destruct n as [|n]; simpl in *.
        by discriminate.
        destruct n as [|n]; simpl in *.
        2: by discriminate.
        unfold leq, subn, subn_rec, eq_op in sup.
        simpl in sup.
        discriminate.
    }
    destruct iL as [|hd iL]; simpl in *.
    all: destruct iL' as [|hd' iL']; simpl in *.
    1-3: rewrite not_all_ind_imp_get_var_type_is_None in get_type.
    1,3,5: by discriminate.
    + apply unfold_access_not_all_ind; auto.
    + destruct iL'; apply unfold_access_not_all_ind; auto.
    + destruct iL; apply unfold_access_not_all_ind; auto.
    + destruct iL; destruct iL'. apply unfold_access_not_all_ind; auto.
    
    

    unfold get_var_type.
    admit.
Admitted.*)

Theorem find_val_imap_find_lemma_lt {A : Type}:
    forall i this (l : list (_ * A)),
        imap.Raw.lt_tree i this ->
        find_val (imap.Raw.elements this ++ l)%list i = find_val l i.
Proof.
    unfold imap.Raw.lt_tree.
    move=> i this; induction this as [|Left HRecL k v Right HRecR]; simpl; trivial.
    move=> l H.
    rewrite <- imap.Raw.Proofs.elements_node.
    rewrite HRecL.
    2: by move=> elt HIn; apply H; constructor; assumption.
    simpl.
    assert (ident_beq i k = false) as HEq.
    {
        rewrite <- Bool.not_true_iff_false.
        rewrite ident_beq_eq; specialize H with k.
        move=> HEq; destruct HEq; move: H.
        impl_tac; [> constructor; reflexivity | idtac ].
        destruct (Ident_as_OT_map.lt_strorder) as [irrefl _].
        unfold Irreflexive, Reflexive, complement in irrefl.
        apply irrefl.
    }
    rewrite HEq; apply HRecR.
    move=> elt HIn; apply H; constructor; assumption.
Qed.

Theorem find_val_imap_find_lemma_gt {A : Type}:
    forall i this (l : list (_ * A)),
        imap.Raw.gt_tree i this ->
        find_val (imap.Raw.elements this ++ l)%list i = find_val l i.
Proof.
    unfold imap.Raw.gt_tree.
    move=> i this; induction this as [|Left HRecL k v Right HRecR]; simpl; trivial.
    move=> l H.
    rewrite <- imap.Raw.Proofs.elements_node.
    rewrite HRecL.
    2: by move=> elt HIn; apply H; constructor; assumption.
    simpl.
    assert (ident_beq i k = false) as HEq.
    {
        rewrite <- Bool.not_true_iff_false.
        rewrite ident_beq_eq; specialize H with k.
        move=> HEq; destruct HEq; move: H.
        impl_tac; [> constructor; reflexivity | idtac ].
        destruct (Ident_as_OT_map.lt_strorder) as [irrefl _].
        unfold Irreflexive, Reflexive, complement in irrefl.
        apply irrefl.
    }
    rewrite HEq; apply HRecR.
    move=> elt HIn; apply H; constructor; assumption.
Qed.

Theorem find_val_end_is_None {A : Type}:
    forall i (l1 l2 : list (_ * A)),
        find_val l2 i = None ->
        find_val l1 i = find_val (l1 ++ l2) i.
Proof.
    move=> i l1 l2; induction l1 as [|[k v] tl HRec]; simpl; auto.
    case ident_beq; trivial.
Qed.

Theorem find_val_is_imap_find:
    forall type_ctxt i,
        imap.find i type_ctxt = @find_val typ (imap.elements type_ctxt) i.
Proof.
    intros.
    destruct type_ctxt as [this is_bst].
    unfold imap.find, imap.elements; simpl.
    induction is_bst as [|id t l r n ibstL HRecL ibstR HRecR Hlt Hgt]; simpl; trivial.
    rewrite <- (cats0 (imap.Raw.elements _)).
    rewrite <- imap.Raw.Proofs.elements_node.
    case Ident_as_OT_map.compare; unfold Ident_as_OT_map.lt, Ident_as_OT_map.eq.
    all: move=> cmp.
    {
        rewrite HRecL.
        apply find_val_end_is_None; simpl.
        assert (ident_beq i id = false) as HEq.
        {
            rewrite <- Bool.not_true_iff_false.
            rewrite ident_beq_eq.
            move=> HEq; destruct HEq; move: cmp.
            destruct (Ident_as_OT_map.lt_strorder) as [irrefl _].
            unfold Irreflexive, Reflexive, complement, Ident_as_OT_map.lt in irrefl.
            apply irrefl.
        }
        rewrite HEq.
        rewrite find_val_imap_find_lemma_gt; auto.
        apply (@imap.Raw.Proofs.gt_tree_trans _ _ i) in Hgt; trivial.
    }
    {
        destruct cmp.
        rewrite find_val_imap_find_lemma_lt; trivial.
        simpl; rewrite ident_beq_refl; trivial.
    }
    {
        rewrite find_val_imap_find_lemma_lt.
        2: by apply (@imap.Raw.Proofs.lt_tree_trans _ _ i) in Hlt; trivial.
        simpl.
        assert (ident_beq i id = false) as HEq.
        2: by rewrite HEq; rewrite app_nil_r; trivial.
        rewrite <- Bool.not_true_iff_false.
        rewrite ident_beq_eq.
        move=> HEq; destruct HEq; move: cmp.
        destruct (Ident_as_OT_map.lt_strorder) as [irrefl _].
        unfold Irreflexive, Reflexive, complement, Ident_as_OT_map.lt in irrefl.
        apply irrefl.
    }
Qed.

Fixpoint get_var_type' (acc : access) (type : option typ) : option typ :=
    match acc with
    | AAll => type
    | ASlice (i::nil) acc =>
        get_var_type' acc
            (type <- type;
            match type with
            | Nat => None
            | Uint dir m _ => Some (Uint dir m 1)
            | Array t _ => Some t
            end)
    | _ => None
    end.

Lemma get_var_type_unfold:
    forall type_ctxt acc v,
    get_var_type type_ctxt (unfold_access acc v)
    = get_var_type' acc (get_var_type type_ctxt v).
Proof.
    move=> type_ctxt acc.
    induction acc as [|[|hd []] acc HRec]; simpl; trivial.
    {
        intros; apply not_all_ind_imp_get_var_type_is_None.
        apply unfold_access_not_all_ind; auto.
    }
    {
        intro; rewrite HRec; trivial.
    }
    {
        intros; apply not_all_ind_imp_get_var_type_is_None.
        apply unfold_access_not_all_ind; auto.
    }
Qed.

Lemma get_var_type'_None:
    forall acc, get_var_type' acc None = None.
Proof.
    move=> acc; induction acc as [|[|h []] acc HRec]; simpl; trivial.
Qed.

Theorem get_var_type'_simpl:
    forall acc d d' m m' n n',
        get_var_type' acc (Some (Uint d m n)) = Some (Uint d' m' n') ->
            acc <> AAll \/ n = 1 ->
                d = d' /\ m = m' /\ 1 = n'.
Proof.
    move=> acc; induction acc as [|[|i []] acc HRec]; simpl; do 6 intro.
    {
        move=> H [Abs|Eq]; inversion H.
        {
            exfalso; apply Abs; reflexivity.
        }
        {
            symmetry in Eq; destruct Eq; auto.
        }
    }
    1,3: by discriminate.
    intros; apply (HRec _ _ _ _ 1); auto.
Qed.

Theorem val_of_type_CoIL {A : Type} :
    forall typ cst l,
        @val_of_type A (CoIL cst) typ l ->
            l = nil /\ typ = Nat.
Proof.
    move=> typ cst; induction typ as [|d [] n|typ HRec ae]; simpl; auto.
    1-3: by move=> l [].
    move=> l; destruct eval_arith_expr.
    2: by move=> [].
    move=> H; apply HRec in H; destruct H.
    discriminate.
Qed.

Theorem val_of_type_CoIR {A : Type}:
    forall typ dir iL form l,
        @val_of_type A (CoIR dir iL (Some form)) typ l ->
        length iL = prod_list form /\ prod_list form <> 0.
Proof.
    move=> typ; induction typ as [|d [m| |] n| typ HRec ae]; simpl.
    1,3,4: by move=> _ iL form _ [].
    all: move=> dir iL form l.
    {
        move=> [-> [H [<- _]]]; auto.
    }
    {
        destruct eval_arith_expr.
        2: by move=> [].
        apply HRec.
    }
Qed.

Theorem expand_var_lemma:
    forall v acc type_ctxt ctxt d m n,
        get_var_type type_ctxt (unfold_access acc v) = Some (Uint d m n) ->
        well_typed_ctxt (imap.elements type_ctxt) ctxt ->
        n <> 0 ->
        eval_var v ctxt acc =
        fold_right (fun i l =>
            l' <- l;
            v' <- eval_var v ctxt (change_access i acc);
            Some (linearize_list_value v' l')) (Some nil) (gen_list_0_int n).
Proof.
    move=> v; induction v as [i|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl.
    {
        move=> acc type_ctxt ctxt d m n Hfind well_typed.
        rewrite get_var_type_unfold in Hfind; simpl in Hfind.
        case_eq (find_val ctxt i).
        {
            move=> c Hfind_val.
            apply (well_typed_ctxt_imp_find_val _ _ i c) in well_typed; trivial.
            destruct well_typed as [typ' [Hfind_type valoType]].
            rewrite find_val_is_imap_find in Hfind.
            rewrite Hfind_type in Hfind.
            destruct c as [cst|dir iL o]; simpl in *.
            {
                move: Hfind valoType.
                clear.
                move=> H valoType.
                apply val_of_type_CoIL in valoType.
                destruct valoType as [_ H'].
                symmetry in H'; destruct H'.
                exfalso.
                destruct acc as [|[|i[]] acc]; simpl in *.
                3: rewrite get_var_type'_None in H.
                all: by discriminate.
            }
            {
                destruct o as [form|]; simpl in *.
                all: swap 1 2.
                {
                    destruct n.
                    by move=> H; exfalso; apply H; reflexivity.
                    move=> _; rewrite gen_list_0_int_S.
                    rewrite fold_right_app; simpl.
                    clear; induction gen_list_0_int as [|hd tl HRec].
                    by simpl; reflexivity.
                    simpl; rewrite <- HRec; reflexivity.
                }
                move=> NotZero.
                pose (p := val_of_type_CoIR _ _ _ _ _ valoType).
                destruct p as [length_eq NotZero'].
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
                    destruct get_access as [x|]; trivial.
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
                destruct get_access; trivial.
                2: by admit.
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
        rewrite VEInd; reflexivity.
    }
    {
        move=> acc type_ctxt ctxt d m n get_type.
        exfalso.
        rewrite not_all_ind_imp_get_var_type_is_None in get_type.
        by discriminate.
        apply unfold_access_not_all_ind; auto.
    }
    {
        move=> acc type_ctxt ctxt d m n get_type.
        exfalso.
        rewrite not_all_ind_imp_get_var_type_is_None in get_type.
        by discriminate.
        apply unfold_access_not_all_ind; auto.
    }
Admitted.

Lemma get_var_imp_valid:
    forall v type_ctxt,
        valid_type_ctxt (imap.elements type_ctxt) ->
    forall typ,
        get_var_type type_ctxt v = Some typ ->
        valid_type typ.
Proof.
    move=> v type_ctxt valid; induction v as [i|v HRec i| |]; simpl.
    3-4: discriminate.
    {
        move=> typ Hfind.
        rewrite find_val_is_imap_find in Hfind.
        apply valid_typed_ctxt_imp_find_val in Hfind; trivial.
    }
    {
        move=> typ.
        destruct (get_var_type) as [[| |t len]|].
        1,4: by discriminate.
        all: move=> H; inversion H as [HEq].
        + constructor; auto.
        + specialize HRec with (Array t len); move: HRec; impl_tac; trivial.
            destruct HEq; move=> HRec; inversion HRec; trivial.
    }
Qed.

Theorem expand_var_inner_soundness:
    forall type_ctxt typ env_it partial v,
        valid_type_ctxt (imap.elements type_ctxt) ->
        well_typed_ctxt (imap.elements type_ctxt) env_it ->
        get_var_type type_ctxt v = Some typ ->
        (forall n, Ensembles.In ident (typ_freevars typ) n -> exists c, find_const env_it n = Some c) ->
            eval_var v env_it AAll
            = fold_right
                (fun v l=> l' <- l; v' <- eval_var v env_it AAll; Some (linearize_list_value v' l'))
                (Some nil) (expand_var_inner typ env_it partial v).
Proof.
    move=> type_ctxt typ env_it partial.
    induction typ as [|d m n|]; simpl.
    {
        move=> v _ _ _ _.
        pose (p := eval_var_linearize_fixpoint env_it v AAll); move: p.
        destruct (eval_var v env_it AAll) as [l|]; trivial.
        move=> HEq; specialize HEq with l; move: HEq.
        impl_tac; trivial.
        move=> ->; reflexivity.
    }
    {
        destruct n as [|n]; simpl.
        {
            move=> v valid _ get_type.
            exfalso.
            apply get_var_imp_valid in get_type; trivial.
            inversion get_type.
            auto.
        }
        destruct n as [|n]; simpl.
        {
            intro v; intros.
            pose (p := eval_var_linearize_fixpoint env_it v AAll); move: p.
            clear.
            case (eval_var v env_it AAll); trivial.
            move=> l H; specialize H with l; move: H.
            impl_tac; [> by reflexivity | idtac ].
            move=> ->; reflexivity.
        }
        move=> v _ well_typed get_type _.
        rewrite (expand_var_lemma _ _ type_ctxt _ d m n.+2); simpl.
        2,3: by assumption.
        2: by discriminate.
        induction (gen_list_0_int n.+2) as [|hd tl HRec]; simpl; trivial.
        rewrite <- HRec; clear HRec.
        cbn.
        assert ((Z.of_nat hd <? 0)%Z = false) as HEq.
        2: rewrite HEq; rewrite Nat2Z.id; reflexivity.
        rewrite Z.ltb_ge.
        exact (Nat2Z.is_nonneg _).
    }
    {
        admit.
    }
Admitted.
