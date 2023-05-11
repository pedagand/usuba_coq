From Usuba Require Import
    ident usuba_AST usuba_ASTProp arch collect usuba_sem usuba_semProp equiv_rel utils
    coq_missing_lemmas.
Require Import Lia.
Require Import OrderedType.
Require Import ZArith.
From mathcomp Require Import ssrnat seq.

Fixpoint get_var_type_inner (typ : option typ) (ind : seq indexing) :=
    match ind with
    | nil => typ
    | _::tl =>
        let typ' := match typ with
        | Some (Nat) => None
        | Some (Array _ 0) => None
        | Some (Array t _) => Some t
        | Some (Uint _ _) => None
        | None => None
        end in
        get_var_type_inner typ' tl
    end.

Definition get_var_type (env_var : imap.t typ) (v : var) :=
    match v with
    | Var x => imap.find x env_var
    | Index (Var x) ind =>
        get_var_type_inner (imap.find x env_var) ind
    | _ => None
    end.

Definition gen_list_0_int (n : nat) : list nat :=
    let fix aux n acc := match n with
        | 0 => acc
        | S n' => aux n' (n' :: acc) 
    end in aux n nil.

Fixpoint expand_var_inner (typ : typ) (partial : bool) (ind : list indexing) : list indexing :=
    match typ with
    | Nat => ind
    | Uint _ _ => ind
    | Array typ len =>
        if partial then
            ind ++ [:: ISlice (map (fun i => Const_e (Z.of_nat i)) (gen_list_0_int len))]
        else
            expand_var_inner typ partial (ind ++ [:: ISlice (map (fun i => Const_e (Z.of_nat i)) (gen_list_0_int len))])
    end.

Definition expand_var (env_var : imap.t typ) (partial : bool) (v : var) : var :=
    match get_var_type env_var v with
    | None => v
    | Some typ =>
        match v with
        | Var var => match expand_var_inner typ partial nil with
            | nil => Var var
            | l => Index (Var var) l
            end
        | Index (Var var) ind => Index (Var var) (expand_var_inner typ partial ind)
        | _ => v
        end
    end.

From mathcomp Require Import all_ssreflect.

Fixpoint get_var_type_inner' (typ : option typ) (acc : access) :=
    match acc with
    | AAll => typ
    | AInd _ acc | ASlice _ acc =>
        let typ' := match typ with
        | Some (Nat) => None
        | Some (Array _ 0) => None
        | Some (Array t _) => Some t
        | Some (Uint _ _) => None
        | None => None
        end in
        get_var_type_inner' typ' acc
    end.

Fixpoint expand_access (acc : access) : list access :=
    match acc with
    | AAll => [:: AAll]
    | AInd i tl => map (AInd i) (expand_access tl)
    | ASlice nil tl => map (ASlice nil) (expand_access tl)
    | ASlice iL tl =>
        flat_map (fun i => map (AInd i) (expand_access tl)) iL 
    end.

Theorem expand_access_not_empty:
    forall acc, expand_access acc <> nil.
Proof.
    move=> acc; induction acc as [|i acc HRec|iL acc HRec]; simpl.
    by discriminate.
    by destruct expand_access.
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

Lemma remove_option_from_list_app_Some {A : Type}:
    forall (l1 : list A) l2 l3 l4,
        remove_option_from_list l2 = Some l1 ->
        remove_option_from_list l4 = Some l3 ->
        remove_option_from_list (l2 ++ l4) = Some (l1 ++ l3).
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
        pose (p := HRec l); move: p.
        do 2 (impl_tac; auto).
        clear.
        destruct remove_option_from_list; simpl.
        2: discriminate.
        move=> H; inversion H; reflexivity.
    }
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

Fixpoint simplify (acc : access) (form : list nat) : list nat :=
    match acc with
    | AAll => form
    | AInd _ acc => simplify acc form
    | ASlice _ acc => match form with
        | nil => nil
        | _::tl => simplify acc tl
        end
    end.

Theorem Forall_nth_error {A : Type} {P : A -> Prop}:
    forall n l e, nth_error l n = Some e -> Forall P l -> P e.
Proof.
    move=> n; induction n as [|n HRec]; move=> [|hd tl]; simpl.
    1,3: by discriminate.
    {
        move=> e HEq; inversion HEq.
        move=> HForall; inversion HForall; assumption.
    }
    {
        move=> e nth HForall; inversion HForall.
        apply (HRec tl); auto.
    }
Qed.

Lemma get_access_same_form:
    forall acc form vL1 vL2,
            match get_access vL1 acc form with
            | Some (_, form1) => match get_access vL2 acc form with
                | Some (_, form2) => form1 = form2
                | None => True
                end
            | None => True
            end.
Proof.
    intro acc; induction acc as [|i acc HRec|iL acc HRec]; simpl; trivial.
    {
        destruct form as [|f_hd f_tl]; trivial.
        move=> vL1 vL2.
        destruct (_ =? _); trivial.
        destruct split_into_segments as [vL1'|]; trivial.
        destruct (length vL2 mod _ =? _); trivial.
        2: match goal with |- match ?f with Some _ => _ | None => _ end => destruct f as [[]|] end; trivial.
        destruct split_into_segments as [vL2'|]; trivial.
        2: match goal with |- match ?f with Some _ => _ | None => _ end => destruct f as [[]|] end; trivial.
        destruct (nth_error vL1') as [v1|]; trivial.
        destruct (nth_error vL2') as [v2|]; trivial.
        2: match goal with |- match ?f with Some _ => _ | None => _ end => destruct f as [[]|] end; trivial.
        apply HRec.
    }
    {
        destruct iL as [|hd tl]; trivial.
        destruct form as [|f_hd f_tl]; trivial.
        move=> vL1 vL2.
        destruct (_ =? _); trivial.
        destruct split_into_segments as [vL1'|]; trivial.
        destruct (length vL2 mod _ =? _); trivial.
        2: match goal with |- match ?f with Some _ => _ | None => _ end => destruct f as [[]|] end; trivial.
        destruct split_into_segments as [vL2'|]; trivial.
        2: match goal with |- match ?f with Some _ => _ | None => _ end => destruct f as [[]|] end; trivial.
        move: (hd :: tl) (HRec f_tl); clear.
        move=> l; case_eq (length l =? 1).
        {
            destruct l as [|h1 []]; simpl.
            1,3: discriminate.
            move=> _ HRec.
            destruct (nth_error vL1') as [v1|]; trivial.
            destruct (nth_error vL2') as [v2|].
            2: match goal with |- match ?f with Some _ => _ | None => _ end => destruct f as [[]|] end; trivial.
            specialize HRec with v1 v2.
            do 2 (destruct get_access as [[]|]; trivial).
            f_equal; assumption.
        }
        move=> _ SameAccess.
        induction l as [|hd tl HRec]; simpl; trivial.
        destruct fold_right as [[]|]; trivial.
        destruct (nth_error vL1') as [v1|]; trivial.
        destruct fold_right as [[]|].
        2: match goal with |- match ?f with Some _ => _ | None => _ end => destruct f as [[]|] end; trivial.
        destruct (nth_error vL2') as [v2|]; trivial.
        2: match goal with |- match ?f with Some _ => _ | None => _ end => destruct f as [[]|] end; trivial.
        specialize SameAccess with v1 v2.
        destruct get_access as [[]|]; trivial.
        destruct get_access as [[]|]; trivial.
        f_equal; assumption.
    }
Qed.

Lemma get_access_form_expand_access:
    forall acc form vL,
        get_access vL acc form <> None ->
        match get_access vL acc form with
        | None => False
        | Some (_, form1) => Forall (fun acc' => match get_access vL acc' form with
            | None => True
            | Some (_, form2) => form2 = simplify acc form1
        end) (expand_access acc)
    end.
Proof.
    intro acc; induction acc as [|i acc HRec|iL acc HRec]; simpl; trivial.
    {
        move=> form vL _.
        constructor; simpl; [> reflexivity | constructor ].
    }
    {
        move=> [|form_hd form_tl] vL; [> by idtac | idtac].
        case_eq (length vL mod form_hd =? 0); [> idtac | by idtac].
        case_eq (split_into_segments form_hd (length vL / form_hd) vL); [> idtac | by idtac ].
        move=> l split_eq mod_eq; simpl.
        case_eq (nth_error l i); [> idtac | by idtac ].
        move=> v nth_err_eq NoErr.
        specialize HRec with form_tl v; move: HRec; impl_tac; trivial; move=> HRec.
        destruct get_access as [[]|]; [> idtac | by idtac ].
        rewrite Forall_map; simpl.
        rewrite mod_eq; rewrite split_eq; rewrite nth_err_eq; assumption.
    }
    {
        destruct iL as [|h1 iL]; [> by idtac | idtac].
        move=> [|form_hd form_tl] vL; [> by idtac | idtac].
        move: (HRec form_tl); clear HRec; move=> HRec.
        case_eq (length vL mod form_hd =? 0); [> idtac | by idtac].
        case_eq (split_into_segments form_hd (length vL / form_hd) vL); [> idtac | by idtac ].
        move=> l split_eq mod_eq; simpl.
        case_eq (nth_error l h1).
        2: by destruct fold_right as [[]|].
        move=> l1 nth_h1_eq; move: (HRec l1); move=> HRec_l1.
        move: (get_access_same_form acc form_tl l1); move=> SameAccess1.
        destruct (get_access l1) as [[l1_out form_l1]|].
        2: by destruct fold_right as [[]|].
        move=> NoErr.
        assert (Forall (fun v => (v' <- v; get_access v' acc form_tl) <> None) [seq nth_error l i | i <- iL]) as NoErr'.
        {
            move: NoErr.
            match goal with |- match match ?f with Some _ => _ | None => _ end
            with Some _ => _ | None => _ end <> None -> _ => move=> NoErr; assert (f <> None) as NoErr'; [> case_eq f | idtac]
            end.
            by discriminate.
            by (move=> H; rewrite H in NoErr).
            move: NoErr'; clear.
            induction iL as [|hd tl HRec]; simpl; move=> NoErr; constructor.
            {
                destruct fold_right as [[]|].
                2: by idtac.
                destruct nth_error; trivial.
                by destruct get_access.
            }
            apply HRec.
            by destruct fold_right.
        }
        destruct fold_right as [[]|]; [> clear NoErr | by idtac ].
        rewrite Forall_app; split.
        {
            rewrite Forall_map; rewrite Forall_map in NoErr'; simpl in *.
            rewrite mod_eq; rewrite split_eq; rewrite nth_h1_eq.
            move: HRec_l1; impl_tac; [> by idtac | idtac].
            clear; move=> H; induction H; constructor; trivial.
        }
        {
            move: HRec_l1 SameAccess1 HRec NoErr'.
            impl_tac; [> by idtac | idtac ].
            rewrite Forall_flat_map; rewrite Forall_map.
            move: mod_eq split_eq.
            clear.
            move=> mod_eq split_eq.
            move=> H SameAccess HRec NoErr.
            induction NoErr as [|hd tl NoErr_hd NoErr_tl HRec']; constructor; trivial.
            rewrite Forall_map; simpl.
            rewrite mod_eq; rewrite split_eq.
            clear HRec'.
            destruct (nth_error _ hd) as [v|]; [> idtac | by idtac ].
            apply HRec in NoErr_hd; clear NoErr_tl HRec.
            specialize SameAccess with v.
            destruct get_access as [[]|].
            2: by destruct NoErr_hd.
            destruct SameAccess; assumption.
        }
    }
Qed.

Theorem get_access_expand_access:
    forall acc form vL,
        omap fst (get_access vL acc form) =
        omap flatten
        (remove_option_from_list
            (map (fun acc' => omap fst (get_access vL acc' form))
                (expand_access acc))).
Proof.
    intro acc; induction acc as [|ind acc HRec|iL acc HRec]; simpl.
    {
        intros; rewrite cats0; reflexivity.
    }
    all: intros [|form_hd form_tl] vL; simpl.
    {
        move: (expand_access_not_empty acc); destruct expand_access; simpl.
        all: by idtac.
    }
    {
        rewrite <-map_comp; unfold comp; simpl.
        destruct (_ =? _); simpl.
        2: by move: (expand_access_not_empty acc); destruct expand_access; simpl.
        destruct split_into_segments; simpl.
        2: by move: (expand_access_not_empty acc); destruct expand_access; simpl.
        destruct nth_error; simpl.
        2: by move: (expand_access_not_empty acc); destruct expand_access; simpl.
        apply HRec.
    }
    {
        destruct iL; simpl.
        {
            rewrite <-map_comp; unfold comp.
            simpl.
            pose (p := expand_access_not_empty acc); move: p; move=> p.
            destruct expand_access; simpl; by idtac.
        }
        {
            rewrite map_cat.
            rewrite remove_option_from_list_app2; auto.
            pose (p := expand_access_not_empty acc); move: p; move=> p.
            destruct expand_access; simpl; trivial.
            exfalso; apply p; reflexivity.
        }
    }
    {
        destruct iL as [|i1 tl]; simpl.
        {
            rewrite <- map_comp; unfold comp; simpl.
            pose (p := expand_access_not_empty acc); move: p.
            destruct expand_access; by simpl.
        }
        {
            rewrite map_cat; rewrite <- map_comp; unfold comp; simpl.
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
            2: destruct fold_right as [[]|]; trivial; destruct nth_error; trivial.
            (* assert (forall l, [seq omap fst match match get_access l x form_tl with
                | Some (l0, dim) => Some (l0 ++ [::], dim)
                | None => None end with
                | Some p => let (l', dim') := p in Some (l', dim')
                | None => None end | x <- expand_access acc]
                = [seq omap fst (get_access l acc' form_tl) | acc' <- expand_access acc]) as HEq.
            {
                clear; move=> l.
                induction expand_access as [|h tl HRec]; simpl; trivial.
                destruct get_access as [[]|]; f_equal; auto.
                rewrite cats0; reflexivity.
            }
            do 2 rewrite HEq. *)
            pose (p1 := HRec form_tl l1); move:p1; move=> p1.
            case_eq (remove_option_from_list [seq omap fst (get_access l1 acc' form_tl) | acc' <- expand_access acc]).
            all: swap 1 2.
            {
                simpl; intro H.
                rewrite H in p1.
                rewrite remove_option_from_list_app2; trivial.
                destruct fold_right as [[]|]; auto.
                do 2 destruct get_access as [[]|]; auto.
                all: simpl in p1; discriminate p1.
            }
            move=> l1' HEq_l1.
            rewrite HEq_l1 in p1.
            destruct (get_access l1) as [[]|]; simpl in *.
            2: by discriminate.
            inversion p1 as [H]; clear p1 H l.
            match goal with
            | |- omap fst match match ?f  with Some _ => _ | None => _ end with Some _ => _ | None => _ end
                = omap flatten (remove_option_from_list (_ ++ ?l)) =>
                    assert (omap fst f = omap flatten (remove_option_from_list l)) as HEq';
                    [> idtac | destruct f as [[]|]; simpl in * ]
            end.
            all: swap 1 2.
            {
                apply remove_option_from_list_lemma.
                by rewrite HEq_l1; auto.
                by assumption.
            }
            all: swap 1 2.
            {
                rewrite remove_option_from_list_app3; auto.
                match goal with | |- ?l = _ => destruct l end; trivial.
                discriminate.
            }
            move: (HRec form_tl) split_Eq mod_Eq; clear; move=> HRec split_Eq mod_Eq.
            induction tl as [|hd tl HRec']; simpl; trivial.
            rewrite map_cat; rewrite <- map_comp; unfold comp; simpl.
            rewrite mod_Eq; rewrite split_Eq.
            destruct nth_error; swap 1 2.
            {
                rewrite remove_option_from_list_app2.
                + clear; simpl; destruct fold_right as [[]|]; simpl; reflexivity.
                + clear; move: (expand_access_not_empty acc); by destruct expand_access.
            }
            pose (p := HRec l); move: p; clear HRec; move=> p.
            case_eq (remove_option_from_list [seq omap fst (get_access l acc' form_tl) | acc' <- expand_access acc]); simpl.
            all: swap 1 2.
            {
                intro H.
                rewrite H in p; simpl in p.
                rewrite remove_option_from_list_app2; trivial; simpl.
                clear HRec'.
                destruct fold_right as [[]|]; auto.
                destruct get_access as [[]|]; auto.
                simpl in p; discriminate p.
            }
            move=> l_top HEq1.
            rewrite HEq1 in p; simpl in p.
            destruct get_access as [[l0 dim']|]; simpl in *.
            2: discriminate p.
            inversion p as [H]; clear H p l0.
            match goal with |- _ = omap flatten (remove_option_from_list (_ ++ ?l)) => case_eq (remove_option_from_list l) end.
            all: swap 1 2.
            {
                intro H; rewrite H in HRec'.
                rewrite remove_option_from_list_app3; trivial.
                destruct fold_right as [[]|]; auto.
                simpl in HRec'; discriminate HRec'.
            }
            intros l_tail HEq2; rewrite HEq2 in HRec'.
            destruct fold_right as [[l0 l1]|]; simpl in HRec'.
            2: discriminate.
            inversion HRec' as [H]; clear H HRec' l0 l1.
            simpl.
            apply remove_option_from_list_lemma.
            + rewrite HEq1; auto.
            + rewrite HEq2; auto.
        }
    }
Qed.

Fixpoint add_all acc n :=
    match acc with
    | AAll => ASlice (gen_list_0_int n) acc
    | AInd i acc => AInd i (add_all acc n)
    | ASlice iL acc => ASlice iL (add_all acc n)
    end.

Inductive well_bounded : access -> list nat -> nat -> Prop :=
    | wb_Bot : forall n l, well_bounded AAll (n::l) n
    | wb_Ind : forall acc form n ind l, well_bounded acc form n ->
        l <> 0 ->
        well_bounded (AInd ind acc) (l::form) n
    | wb_Slice : forall acc form n ind l, well_bounded acc form n ->
        l <> 0 ->
        well_bounded (ASlice ind acc) (l::form) n.

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

Theorem gen_list_0_int_lemma': 
    forall n, forall l : list nat,
        ((fix aux (n : nat) (acc : seq nat) {struct n} : seq nat :=
            match n with
            | 0 => acc
            | n'.+1 => aux n' (n' :: acc)
            end) n l = (fix aux (n : nat) (acc : seq nat) {struct n} : seq nat :=
            match n with
            | 0 => acc
            | n'.+1 => aux n' (n' :: acc)
            end) n nil ++ l)%list.
Proof.
    induction n as [|n HRec]; simpl; trivial.
    move=> l.
    rewrite HRec.
    specialize HRec with [:: n].
    rewrite HRec.
    rewrite <- app_assoc; simpl.
    reflexivity.
Qed.

Theorem gen_list_0_int_S':
    forall n, gen_list_0_int (S n) = (gen_list_0_int n ++ n::nil)%list.
Proof.
    unfold gen_list_0_int.
    induction n; simpl; trivial.
    do 2 rewrite (gen_list_0_int_lemma _ (_::_)).
    rewrite <- app_assoc; simpl.
    reflexivity.
Qed.

Theorem  gen_list_0_int_Forall:
    forall n, Forall (fun i => i < n)%coq_nat (gen_list_0_int n).
Proof.
    move=> n; induction n as [|h HRec].
    {
        unfold gen_list_0_int; constructor.
    }
    {
        rewrite gen_list_0_int_S; apply Forall_app; split.
        {
            induction gen_list_0_int; constructor.
            all: inversion HRec; auto.
        }
        {
            constructor; auto.
        }
    }
Qed.

Lemma len_gen_list:
    forall n, length (gen_list_0_int n) = n.
Proof.
    move=> n; induction n as [|n HRec]; simpl; trivial.
    rewrite gen_list_0_int_S; rewrite length_app; simpl.
    rewrite addn1; rewrite HRec; reflexivity.
Qed.

Lemma nth_gen_list_length {A : Type}:
    forall n (iL : list A),
        length iL = n ->
        [seq nth_error iL i | i <- gen_list_0_int n] = map Some iL.
Proof.
    move=> n; induction n as [|n HRec]; simpl.
    {
        move=> []; by simpl.
    }
    {
        move=> iL; destruct (case_last iL) as [->|[front [last ->]]]; simpl.
        by discriminate.
        rewrite length_app; simpl; rewrite addn1.
        rewrite gen_list_0_int_S; do 2 rewrite map_cat; simpl.
        move=> lengthEq'; inversion lengthEq' as [lengthEq]; clear lengthEq'.
        rewrite <- HRec; trivial.
        f_equal.
        {
            rewrite <- lengthEq; clear.
            move: (gen_list_0_int_Forall (length front)).
            induction gen_list_0_int; simpl; trivial.
            move=> Hforall; inversion Hforall as [|x l' H]; f_equal; auto.
            rewrite nth_error_app1; trivial.            
        }
        {
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl; trivial.
        }
    }
Qed.

Lemma empty_disj {A : Type} (l : list A): {l = nil} + {l <> nil}.
Proof.
    destruct l; auto.
    right; discriminate.
Qed.

Theorem get_access_add_all_slice:
    forall acc form n,
        well_bounded acc form n ->
    forall iL,
        length iL = prod_list form ->
        n <> 0 ->
        get_access iL acc form =
        get_access iL (add_all acc n) form.
Proof.
    move=> acc; induction acc as [|ind acc HRec|indL acc HRec]; simpl.
    {
        move=> form n wellB iL; inversion wellB; simpl.
        move=> lengthEq NotZero; rewrite lengthEq.
        unfold muln, muln_rec.
        rewrite Nat.mul_comm; rewrite Nat.mod_mul; simpl; trivial.
        rewrite Nat.div_mul; trivial.
        destruct (split_into_segments_soundness _ _ _ lengthEq) as [iL' [-> [HForall [<- lengthEq']]]].
        rewrite nth_gen_list_length; trivial.
        move: NotZero.
        rewrite len_gen_list.
        rewrite <- lengthEq'; clear.
        induction iL' as [|hd tl HRec]; simpl; [> by idtac | move=> _].
        destruct (empty_disj tl) as [HEq|HDiff].
        {
            symmetry in HEq; destruct HEq; simpl in *.
            rewrite app_nil_r; rewrite cats0.
            reflexivity.
        }
        move: HRec; impl_tac.
        by destruct tl.
        move=> HRec.
        destruct fold_right as [[]|]; simpl in *.
        2: destruct gen_list_0_int; discriminate.
        rewrite gen_list_0_int_S.
        destruct gen_list_0_int; simpl.
        by discriminate.
        inversion HRec as [H]; clear HRec; destruct H.
        reflexivity.
    }
    {
        move=> form n wellB'; inversion wellB' as [|hd tl n' ind' l wellB NotZero'|].
        clear H H0 H1 H2 n' wellB' hd form; simpl.
        move=> iL lengthEq NotZero; rewrite lengthEq.
        destruct (_ =? _); trivial.
        unfold muln, muln_rec.
        rewrite Nat.mul_comm; rewrite Nat.div_mul; trivial.
        destruct (split_into_segments_soundness _ _ _ lengthEq) as [iL' [-> [HEq _]]].
        move: (@Forall_nth_error _ (fun l => length l = prod_list tl) ind iL').
        destruct nth_error as [l'|]; trivial.
        move=> H; specialize H with l'; move: H; impl_tac; trivial.
        impl_tac; trivial.
        move=> H; apply HRec; trivial.
    }
    {
        move=> form n wellB'; inversion wellB' as [| |hd tl n' ind l wellB NotZero'].
        clear H H0 H1 H2 n' wellB' hd form; simpl.
        move=> iL lengthEq NotZero; rewrite lengthEq.
        destruct (_ =? _); trivial.
        unfold muln, muln_rec.
        rewrite Nat.mul_comm; rewrite Nat.div_mul; trivial.
        destruct (split_into_segments_soundness _ _ _ lengthEq) as [iL' [-> [HEq _]]].
        destruct indL as [|i_hd i_tl]; trivial.
        move: (i_hd::i_tl); move=> indL.
        eq_match.
        induction indL as [|indL_hd indL_tl HRec_indL]; simpl; trivial.
        rewrite HRec_indL; clear HRec_indL; destruct fold_right as [[]|]; trivial.
        move: (@Forall_nth_error _ (fun l => length l = prod_list tl) indL_hd iL').
        destruct nth_error as [l'|]; trivial.
        move=> H; specialize H with l'; move: H; impl_tac; trivial.
        impl_tac; trivial.
        move=> H.
        pose (p := HRec _ _ wellB _ H NotZero); move: p; clear.
        move=> H.
        do 2 destruct get_access as [[]|]; simpl in *; inversion H; reflexivity.
    }
Qed.

Fixpoint change_access (i : nat) (acc : access) : access :=
    match acc with
    | AAll => AInd i AAll
    | AInd n acc => AInd n (change_access i acc)
    | ASlice iL acc => ASlice iL (change_access i acc)
    end.

(* Lemma get_type_var_equiv:
    forall type_ctxt v1 v2,
        var_equiv v1 v2 -> get_var_type type_ctxt v1 = get_var_type type_ctxt v2.
Proof.
    move=> type_ctxt v1 v2 ve; induction ve as [i|v1 v2 ae1 ae2 ve HRec|v1 v2 l1 l2 ve HRec|v1 v2 is1 is2 ie1 ie2 ve HRec]; simpl.
    {
        reflexivity.
    }
    all: rewrite HRec; reflexivity.
Qed. *)

(* Fixpoint not_all_ind (acc : var) : bool :=
    match acc with
    | Var v => false
    | Index v _ => not_all_ind v
    | Slice _ _ | Range _ _ _ => true
    end. *)

(* Lemma not_all_ind_imp_get_var_type_is_None:
    forall v, not_all_ind v = true -> forall type_ctxt, get_var_type type_ctxt v = None.
Proof.
    move=> v; induction v as [v|v HRec ae|v HRec es ee|v HRec iL]; simpl; trivial.
    by discriminate.
    by intros; rewrite HRec; auto.
Qed. *)

(* Lemma unfold_access_not_all_ind:
    forall acc v, not_all_ind v = true -> not_all_ind (unfold_access acc v) = true.
Proof.
    move=> acc; induction acc as [|i acc HRec|iL acc HRec]; simpl; auto.
    move=> v H.
    destruct iL as [|hd tl].
    {
        apply HRec; simpl; reflexivity.
    }
    destruct tl; apply HRec; simpl; trivial.
Qed. *)

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

(* Fixpoint get_var_type' (acc : access) (type : option typ) : option typ :=
    match acc with
    | AAll => type
    | ASlice _ acc | AInd _ acc =>
        get_var_type' acc
            (type <- type;
            match type with
            | Nat => None
            | Uint _ _ => None
            | Array _ 0 => None
            | Array t _ => Some t
            end)
    end. *)

(* Lemma get_var_type_unfold:
    forall type_ctxt acc v,
    get_var_type type_ctxt (unfold_access acc v)
    = get_var_type' acc (get_var_type type_ctxt v).
Proof.
    move=> type_ctxt acc.
    induction acc as [|i acc HRec|iL acc HRec]; simpl; trivial.
    {
        intros; rewrite HRec; simpl; reflexivity.
    }
    {
        intro; rewrite HRec; trivial.
    }
Qed. *)

Lemma get_var_type_inner_None:
    forall indexing, get_var_type_inner None indexing = None.
Proof.
    move=> indexing; induction indexing as [|v ind HRec]; simpl; trivial.
Qed.

Lemma get_var_type_inner'_None:
    forall acc, get_var_type_inner' None acc = None.
Proof.
    move=> acc; induction acc as [|i acc HRec|iL acc HRec]; simpl; trivial.
Qed.

Theorem val_of_type_CoIL {A : Type} :
    forall typ cst l,
        @val_of_type A (CoIL cst) typ l ->
            l = nil /\ typ = Nat.
Proof.
    move=> typ cst; induction typ as [|d []|typ HRec ae]; simpl; auto.
    1-3: by move=> l [].
    move=> l H; apply HRec in H; destruct H.
    destruct l; simpl in H; by idtac.
Qed.

Theorem val_of_type_CoIR {A : Type}:
    forall typ dir iL form l,
        @val_of_type A (CoIR dir iL form) typ l ->
        length iL = prod_list form /\ prod_list form <> 0.
Proof.
    move=> typ; induction typ as [|d [m| |]| typ HRec ae]; simpl.
    1,3,4: by move=> _ iL form _ [].
    all: move=> dir iL form l.
    {
        move=> [-> [H [<- _]]]; auto.
    }
    {
        apply HRec.
    }
Qed.

Theorem val_of_CoIL_abs {A : Type}:
    forall index typ z l d m,
        @val_of_type A (CoIL z) typ l ->
        Some (Uint d m) = get_var_type_inner (Some typ) index -> False.
Proof.
    move=> index; induction index as [|hd tl HRec]; simpl.
    {
        move=> [|d' m'|typ a]; simpl.
        + do 4 intro; discriminate.
        + destruct m'; do 4 intro; move=> [].
        + do 4 intro; discriminate.
    }
    {
        move=> [|d' m' |typ len]; simpl.
        by do 5 intro; rewrite get_var_type_inner_None; discriminate.
        by destruct m'; do 4 intro; move=> [].
        destruct len.
        by rewrite get_var_type_inner_None; idtac.
        do 4 intro; apply HRec.
    }
Qed.

Theorem get_var_type'_wb {A : Type}:
    forall acc typ form iL d' typ' n l,
        n <> 0 ->
        convert_type typ = Some (d', form) ->
        @val_of_type A (CoIR d' iL (l ++ form)) typ l ->
        Some (Array typ' n) = get_var_type_inner' (Some typ) acc ->
        well_bounded acc form n.
Proof.
    move=> acc; induction acc as [|i acc HRec|iL acc HRec]; simpl.
    {
        move=> [|d' m' [n'|]|typ a]; simpl.
        1: by do 8 intro; move=> [].
        by do 7 intro; move=> Abs; inversion Abs.
        by do 8 intro; move=> Abs; inversion Abs.
        {
            do 7 intro; destruct convert_type as [[]|].
            all: move=> HEq; inversion HEq.
            move=> val_of HEq'; inversion HEq'.
            constructor.
        }
    }
    {
        move=> [|d' m'|typ len]; simpl.
        by do 9 intro; rewrite get_var_type_inner'_None; discriminate.
        {
            rewrite get_var_type_inner'_None.
            do 8 intro; discriminate.
        }
        {
            move=> [|form_hd form_tl] iL' d' d typ' l; simpl.
            {
                move=> _ _ val_of; exfalso.
                apply val_of_type_length_leq in val_of.
                rewrite cats0 in val_of; rewrite length_app in val_of.
                simpl in val_of; rewrite addn1 in val_of.
                rewrite ltnn in val_of; discriminate.
            }
            move=> Inf convert val_of get_var_type'.
            move: (HRec typ); clear HRec; move=> HRec.
            move: val_of HRec get_var_type'.
            destruct convert_type as [[]|]; inversion convert.
            move=> val_of HRec get_var_type'.
            destruct form_hd.
            {
                rewrite get_var_type_inner'_None in get_var_type'; discriminate.
            }
            constructor; auto.
            refine (HRec _ _ _ _ _ (_ ++ [:: _ ]) _ _ _ _).
            by assumption.
            by reflexivity.
            by rewrite <-app_assoc; simpl; exact val_of.
            by exact get_var_type'.
        }
    }
    {
        move=> [|d' m'|typ len]; simpl.
        by do 9 intro; rewrite get_var_type_inner'_None; discriminate.
        {
            rewrite get_var_type_inner'_None.
            do 8 intro; discriminate.
        }
        {
            move=> [|form_hd form_tl] iL' d' d typ' l; simpl.
            {
                move=> _ _ val_of; exfalso.
                apply val_of_type_length_leq in val_of.
                rewrite cats0 in val_of; rewrite length_app in val_of.
                simpl in val_of; rewrite addn1 in val_of.
                rewrite ltnn in val_of; discriminate.
            }
            move=> Inf convert val_of get_var_type'.
            move: (HRec typ); clear HRec; move=> HRec.
            move: val_of HRec get_var_type'.
            destruct convert_type as [[]|]; inversion convert.
            move=> val_of HRec get_var_type'.
            destruct form_hd.
            {
                rewrite get_var_type_inner'_None in get_var_type'; discriminate.
            }
            constructor; auto.
            refine (HRec _ _ _ _ _ (_ ++ [:: _ ]) _ _ _ _).
            by assumption.
            by reflexivity.
            by rewrite <-app_assoc; simpl; exact val_of.
            by exact get_var_type'.
        }
    }
Qed.

Lemma val_of_CoIL {A : Type}:
    forall z typ l,
        @val_of_type A (CoIL z) typ l -> l = nil.
Proof.
    move=> z typ; induction typ as [|d m|typ HRec len]; simpl; trivial.
    + by move=> l; destruct m.
    + move=> l val_of; apply HRec in val_of; destruct l; discriminate.
Qed.

Lemma access_of_ind_app_slice_None:
    forall ctxt ind n,
        access_of_ind ctxt ind = None ->
        access_of_ind ctxt (ind ++ [:: ISlice [seq Const_e (Z.of_nat i) | i <- gen_list_0_int n]]) = None.
Proof.
    move=> ctxt ind n; induction ind as [|hd tl HRec]; simpl.
    {
        by discriminate.
    }
    destruct hd.
    {
        destruct eval_arith_expr; trivial.
        destruct (access_of_ind _ tl).
        by idtac.
        rewrite HRec; trivial.
    }
    {
        destruct eval_arith_expr; trivial.
        destruct eval_arith_expr; trivial.
        destruct (access_of_ind _ tl).
        by idtac.
        rewrite HRec; trivial.
    }
    {
        destruct fold_right; trivial.
        destruct (access_of_ind _ tl).
        by idtac.
        rewrite HRec; trivial.
    }
Qed.

Lemma access_of_ind_app_slice:
    forall ctxt ind n acc,
        access_of_ind ctxt ind = Some acc ->
        access_of_ind ctxt (ind ++ [:: ISlice [seq Const_e (Z.of_nat i) | i <- gen_list_0_int n]]) = Some (add_all acc n).
Proof.
    move=> ctxt ind n; induction ind as [|hd tl HRec]; simpl.
    {
        move=> acc HEq; inversion HEq as [H].
        clear H HEq acc; simpl.
        match goal with |- match fold_right ?f (Some nil) ?l with Some _ => _ | None => _ end = _
            => assert (forall l', fold_right f (Some l') l = Some (gen_list_0_int n ++ l')) as HEq end.
        2: rewrite (HEq nil); rewrite cats0; reflexivity.
        induction n as [|n HRec]; simpl.
        {
            unfold gen_list_0_int; reflexivity.
        }
        {
            rewrite gen_list_0_int_S; rewrite map_cat.
            move=> l'.
            rewrite fold_right_app; simpl.
            assert (eval_arith_expr ctxt (Const_e (Z.of_nat n)) = Some n) as ->.
            {
                unfold eval_arith_expr, eval_arith_expr_inner; simpl.
                rewrite Nat2Z.id.
                move :(Nat2Z.is_nonneg n).
                rewrite <- Z.nlt_ge.
                rewrite <- Z.ltb_lt.
                rewrite Bool.not_true_iff_false.
                move=> ->; reflexivity.
            }
            rewrite HRec.
            rewrite <-app_assoc; simpl.
            reflexivity.
        }
    }
    destruct hd; simpl.
    {
        destruct eval_arith_expr as [n'|].
        2: by idtac.
        destruct (access_of_ind _ tl) as [acc'|].
        2: by idtac.
        move=> acc H; inversion H as [H'].
        clear H H'.
        specialize HRec with acc'; rewrite HRec; trivial.
    }
    {
        destruct eval_arith_expr as [n1|].
        2: by idtac.
        destruct eval_arith_expr as [n2|].
        2: by idtac.
        destruct (access_of_ind _ tl) as [acc'|].
        2: by idtac.
        move=> acc H; inversion H as [H'].
        clear H H'.
        specialize HRec with acc'; rewrite HRec; trivial.
    }
    {
        destruct fold_right as [iL|].
        2: by idtac.
        destruct (access_of_ind _ tl) as [acc'|].
        2: by idtac.
        move=> acc H; inversion H as [H'].
        clear H H'.
        specialize HRec with acc'; rewrite HRec; trivial.
    }
Qed.

Lemma access_of_ind_get_var_type:
    forall ctxt ind acc,
        access_of_ind ctxt ind = Some acc ->
        forall typ,
        get_var_type_inner typ ind = get_var_type_inner' typ acc.
Proof.
    move=> ctxt ind; induction ind as [|hd tl HRec]; simpl.
    {
        move=> acc H; inversion H; simpl; trivial.
    }
    destruct hd.
    {
        destruct eval_arith_expr.
        2: by idtac.
        destruct access_of_ind.
        2: by idtac.
        move=> acc' H; inversion H as [H'].
        clear H H' acc'; simpl.
        move=> [[|d m|t [|len']]|]; apply HRec; trivial.
    }
    {
        destruct eval_arith_expr.
        2: by idtac.
        destruct eval_arith_expr.
        2: by idtac.
        destruct access_of_ind.
        2: by idtac.
        move=> acc' H; inversion H as [H'].
        clear H H' acc'; simpl.
        move=> [[|d m|t [|len']]|]; apply HRec; trivial.
    }
    {
        destruct fold_right.
        2: by idtac.
        destruct access_of_ind.
        2: by idtac.
        move=> acc' H; inversion H as [H'].
        clear H H' acc'; simpl.
        move=> [[|d m|t [|len']]|]; apply HRec; trivial.
    }
Qed.

Theorem add_all_var_lemma:
    forall v ind type_ctxt ctxt typ n,
        get_var_type type_ctxt (Index (Var v) ind) = Some (Array typ n) ->
        well_typed_ctxt (imap.elements type_ctxt) ctxt ->
        n <> 0 ->
        eval_var (Index (Var v) ind) ctxt =
        eval_var (Index (Var v) (ind ++ [:: ISlice [seq Const_e (Z.of_nat i) | i <- gen_list_0_int n]])) ctxt.
Proof.
    unfold eval_var; simpl.
    move=> i ind type_ctxt ctxt typ n.
    move: (access_of_ind_app_slice ctxt ind n) (access_of_ind_app_slice_None ctxt ind)
        (access_of_ind_get_var_type ctxt ind).
    destruct access_of_ind as [acc|].
    2: move=> _ ->; trivial.
    move=> H _; specialize H with acc; rewrite H; trivial.
    clear.
    move=> Eq_get_type Hfind well_typed NotZero.
    case_eq (find_val ctxt i); trivial.
    move=> c find_eq.
    apply (well_typed_ctxt_imp_find_val _ _ i c) in well_typed; trivial.
    destruct well_typed as [typ' [Hfind' val_of]].
    assert (Some (Array typ n) = get_var_type_inner' (Some typ') acc) as TypeEq.
    {
        rewrite find_val_is_imap_find in Hfind.
        rewrite <- Eq_get_type; trivial.
        rewrite Hfind' in Hfind.
        auto.
    }
    clear Hfind Hfind' Eq_get_type.
    destruct c as [z|d' iL form]; trivial.
    rewrite (get_access_add_all_slice acc form n); auto.
    {
        apply (get_var_type'_wb _ typ' _ iL d' typ _ nil NotZero); trivial.
        {
            apply (val_of_type_convert iL _ _ _ nil); simpl.
            assumption.
        }
    }
    {
        move: (val_of_type_convert iL typ' d' form nil); simpl.
        impl_tac; trivial.
        move=> H.
        apply (val_of_type_len _ _ _ d' _ form) in val_of; trivial.
        destruct val_of as [_ <-]; simpl; trivial.
    }
Qed.

(*
Theorem expand_access_eval_var_lemma:
    forall v acc type_ctxt ctxt typ n,
        get_var_type type_ctxt (Index (Var v) index) = Some (Array typ n) ->
        well_typed_ctxt (imap.elements type_ctxt) ctxt ->
        n <> 0 ->
        eval_var (Index (Var v) index) ctxt =
        fold_right (fun acc' l =>
            l' <- l;
            v' <- eval_var v ctxt acc';
            Some (linearize_list_value v' l')) (Some nil) (expand_access acc).
Proof.
    move=> v; induction v as [i|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl.
    {
        move=> acc type_ctxt ctxt typ n Hfind well_typed.
        rewrite get_var_type_unfold in Hfind; simpl in Hfind.
        case_eq (find_val ctxt i).
        move=> c Hfind_val.
        apply (well_typed_ctxt_imp_find_val _ _ i c) in well_typed; trivial.
        destruct well_typed as [typ' [Hfind_type valoType]].
        rewrite find_val_is_imap_find in Hfind.
        rewrite Hfind_type in Hfind.
        destruct c as [cst|dir iL form]; simpl in *.
        {
            move: Hfind valoType.
            clear.
            move=> H valoType.
            apply val_of_type_CoIL in valoType.
            destruct valoType as [_ H'].
            symmetry in H'; destruct H'.
            exfalso.
            destruct acc; simpl in *.
            by discriminate.
            all: rewrite get_var_type'_None in H; discriminate.
        }
        {
            move=> NotZero.
            pose (p := val_of_type_CoIR _ _ _ _ _ valoType).
            destruct p as [length_eq NotZero'].
            move: (get_access_expand_access acc form iL).
            move: (get_access_form_expand_access acc form iL).
            destruct get_access as [[iL' form']|]; simpl.
            {
                impl_tac; [> by idtac | idtac ].
                case_eq (remove_option_from_list [seq omap fst (get_access iL acc' form)| acc' <- expand_access acc]); simpl.
                2: discriminate.
                move=> l HEq HForall H; inversion H; move: HForall HEq.
                clear.
                move=> HForall.
                move: (expand_access_not_empty acc).
                induction HForall as [|hd tl P_hd P_tl HRec]; simpl.
                by idtac.
                move=> _.
                destruct get_access as [[]|]; simpl.
                2: discriminate.
                destruct (empty_disj tl) as [HEq|HEq].
                {
                    symmetry in HEq; destruct HEq; simpl in *.
                    move=> H; inversion H; simpl.
                    rewrite cats0.
                    rewrite P_hd.
                    admit.
                }
                admit.
            }
            admit.
        }
        admit.
    }
Admitted.



Theorem expand_var_lemma:
    forall v acc type_ctxt ctxt typ n,
        get_var_type type_ctxt (unfold_access acc v) = Some (Array typ n) ->
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
        move=> acc type_ctxt ctxt typ n Hfind well_typed.
        rewrite get_var_type_unfold in Hfind; simpl in Hfind.
        case_eq (find_val ctxt i).
        {
            move=> c Hfind_val.
            apply (well_typed_ctxt_imp_find_val _ _ i c) in well_typed; trivial.
            destruct well_typed as [typ' [Hfind_type valoType]].
            rewrite find_val_is_imap_find in Hfind.
            rewrite Hfind_type in Hfind.
            destruct c as [cst|dir iL form]; simpl in *.
            {
                move: Hfind valoType.
                clear.
                move=> H valoType.
                apply val_of_type_CoIL in valoType.
                destruct valoType as [_ H'].
                symmetry in H'; destruct H'.
                exfalso.
                destruct acc as [|[|i[]] acc]; simpl in *.
                by discriminate.
                all: rewrite get_var_type'_None in H; discriminate.
            }
            {
                move=> NotZero.
                pose (p := val_of_type_CoIR _ _ _ _ _ valoType).
                destruct p as [length_eq NotZero'].
                all: admit.
(*                rewrite (get_access_split _ _ n); trivial.
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
                *)
            }
        }
        {
            destruct n as [].
            {
                move=> _ NotZero; exfalso; apply NotZero; reflexivity.
            }
            {
                intros.
                rewrite gen_list_0_int_S'; rewrite fold_right_app; simpl.
                clear; induction gen_list_0_int as [|hd tl HRec]; simpl; trivial.
                rewrite <- HRec; reflexivity.
            }
        }
    }
    {
        move=> acc type_ctxt ctxt typ n.
        case (eval_arith_expr ctxt ae).
        all: swap 1 2.
        {
            move=> _ _ NotZero.
            destruct n as [].
            by exfalso; apply NotZero; reflexivity.
            rewrite gen_list_0_int_S'; rewrite fold_right_app; simpl; trivial.
            clear; induction gen_list_0_int as [|hd tl HRec]; simpl; trivial.
            rewrite <- HRec; reflexivity.
        }
        move=> i get_type well_typed not_zero.
        specialize HRec with (ASlice [:: i] acc) type_ctxt ctxt typ n.
        simpl in HRec.
        rewrite <- HRec; trivial.
        rewrite <- get_type.
        apply get_type_var_equiv.
        rewrite VEInd; reflexivity.
    }
    {
        admit.
    }
    {
        admit.
    }
Admitted.*)

Lemma get_var_imp_valid:
    forall v type_ctxt,
        valid_type_ctxt (imap.elements type_ctxt) ->
    forall typ,
        get_var_type type_ctxt v = Some typ ->
        valid_type typ.
Proof.
    move=> v type_ctxt valid; induction v as [i|v HRec ind]; simpl.
    {
        move=> typ Hfind.
        rewrite find_val_is_imap_find in Hfind.
        apply valid_typed_ctxt_imp_find_val in Hfind; trivial.
    }
    destruct v.
    2: by idtac.
    simpl in *.
    destruct imap.find as [t|].
    2: by rewrite get_var_type_inner_None.
    specialize HRec with t; move: HRec.
    impl_tac; trivial.
    clear; move: t.
    induction ind as [|hd tl HRec]; simpl.
    {
        move=> t vt t' H; move: vt; inversion H; trivial.
    }
    {
        move=> [| |typ [| len]] vtyp.
        1-3: by rewrite get_var_type_inner_None.
        inversion vtyp.
        apply HRec; assumption.
    }
Qed.

Lemma get_var_type_inner_app:
    forall ind1 ind2 typ,
        get_var_type_inner typ (ind1 ++ ind2) = get_var_type_inner (get_var_type_inner typ ind1) ind2.
Proof.
    move=> ind1; induction ind1 as [|hd tl HRec]; simpl; trivial.
Qed.

Lemma expand_var_extend:
    forall typ partial ind,
        length ind <= length (expand_var_inner typ partial ind).
Proof.
    move=> typ; induction typ as [| |typ HRec len]; simpl.
    1,2: by idtac.
    move=> [] ind.
    {
        rewrite length_app; simpl.
        rewrite addn1.
        apply leqnSn.
    }
    {
        refine (leq_trans _ (HRec _ _)).
        rewrite length_app; simpl.
        rewrite addn1; apply leqnSn.
    }
Qed.

Theorem expand_var_inner_soundness:
    forall type_ctxt typ env_it partial v,
        valid_type_ctxt (imap.elements type_ctxt) ->
        well_typed_ctxt (imap.elements type_ctxt) env_it ->
        get_var_type type_ctxt v = Some typ ->
            eval_var v env_it = eval_var (expand_var type_ctxt partial v) env_it.
Proof.
    move=> type_ctxt typ env_it partial.
    unfold expand_var.
    induction typ as [|d m|typ HRec len]; simpl.
    {
        move=> v _ _ ->.
        destruct v as [v|[] len]; simpl; trivial.
    }
    {
        move=> v _ _ ->.
        destruct v as [|[] len]; simpl; reflexivity.
    }
    {
        move=> v valid_type well_typed get_type.
        rewrite get_type; simpl.
        assert (len <> 0) as NotZero.
        {
            apply get_var_imp_valid in get_type; trivial.
            inversion get_type; trivial.
        }
        destruct v as [v|[v|] ind]; simpl.
        3: by reflexivity.
        {
            transitivity (eval_var (Index (Var v) [:: ISlice [seq Const_e (Z.of_nat i) | i <- gen_list_0_int len]]) env_it).
            {
                move: (add_all_var_lemma v nil type_ctxt env_it typ len); simpl.
                move=> <-; trivial.
                unfold eval_var; simpl.
                case_eq (find_val env_it v); trivial.
                move=> c Eq.
                destruct (well_typed_ctxt_imp_find_val _ _ _ _ well_typed Eq) as [typ' [find val_of_type]].
                unfold get_var_type in get_type.
                rewrite find_val_is_imap_find in get_type.
                rewrite get_type in find.
                move: val_of_type; inversion find as [H'].
                clear H' find typ'.
                destruct c; trivial.
                simpl.
                move=> Abs; apply val_of_CoIL in Abs.
                inversion Abs.
            }
            {
                destruct partial; trivial.
                rewrite HRec; trivial.
                all: unfold get_var_type; unfold get_var_type in get_type; simpl.
                all: rewrite get_type; destruct len; auto.
                1,3: by idtac.
                move: (expand_var_extend typ false [:: ISlice
                        [seq Const_e (Z.of_nat i) | i <- gen_list_0_int len.+1]]).
                destruct expand_var_inner; trivial.
                simpl.
                by idtac.
            }
        }
        {
            rewrite (add_all_var_lemma _ _ type_ctxt _ typ len); trivial.
            destruct partial; trivial.
            rewrite HRec; trivial.
            all: unfold get_var_type; rewrite get_var_type_inner_app.
            all: unfold get_var_type in get_type; rewrite get_type; simpl.
            all: by destruct len.
        }
    }
Qed.
