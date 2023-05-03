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
        | Some (Array _ 0) => None
        | Some (Array t _) => Some t
        | Some (Uint _ _ (Some 0)) => None
        | Some (Uint dir m (Some n)) =>
            Some (Uint dir m None)
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
    | Uint _ _ None => v::nil
    | Uint _ _ (Some n) =>
        map (fun i => Index v (Const_e (Z.of_nat i))) (gen_list_0_int n)
    | Array typ len =>
        if partial then
            List.map (fun i => Index v (Const_e (Z.of_nat i))) (gen_list_0_int len)
        else
            flat_map
            (fun i => expand_var_inner typ env_it partial (Index v (Const_e (Z.of_nat i))))
            (gen_list_0_int len)
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

Theorem get_access_expand_access:
    forall acc form vL,
        omap fst (get_access vL acc form) =
        omap flatten
        (remove_option_from_list
            (map (fun acc' => omap fst (get_access vL acc' form))
                (expand_access acc))).
Proof.
    intro acc; induction acc as [|iL acc HRec]; simpl.
    {
        intros; destruct remove_option_from_list; simpl; trivial.
        rewrite cats0; reflexivity.
    }
    all: intros [|form_hd form_tl] vL.
    {
        destruct iL as [|h []]; simpl.
        {
            rewrite <-map_comp.
            unfold comp.
            simpl.
            pose (p := expand_access_not_empty acc); move: p; move=> p.
            destruct expand_access; simpl; by idtac.
        }
        {
            rewrite <-map_comp; unfold comp; simpl.
            pose (p := expand_access_not_empty acc); move: p; move=> p.
            destruct expand_access; simpl; by idtac.
        }
        {
            do 2 rewrite map_cat.
            rewrite remove_option_from_list_app2; auto.
            pose (p := expand_access_not_empty acc); move: p; move=> p.
            destruct expand_access; simpl; trivial.
            exfalso; apply p; reflexivity.
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
            destruct split_into_segments as [l|].
            2: pose (p := expand_access_not_empty acc); move: p.
            2: destruct expand_access; by simpl.
            destruct nth_error as [l0|].
            2: pose (p := expand_access_not_empty acc); move: p.
            2: destruct expand_access; by simpl.
            specialize HRec with form_tl l0.
            destruct get_access as [[]|]; simpl in *.
            1: rewrite cats0.
            all: rewrite HRec; clear.
            all: f_equal; f_equal.
            all: induction expand_access as [|hd tl HRec]; simpl; trivial.
            all: rewrite <- HRec.
            all: destruct get_access as [[]|]; auto.
            all: rewrite cats0; reflexivity.
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
            2: destruct fold_right as [[]|]; trivial; destruct nth_error; trivial.
            2: destruct get_access as [[]|]; trivial.
            destruct nth_error as [l2|].
            all: swap 1 2.
            {
                rewrite remove_option_from_list_app3.
                2: apply remove_option_from_list_app2.
                2: pose (p := expand_access_not_empty acc); move: p.
                2: destruct expand_access; by simpl.
                destruct fold_right as [[]|]; simpl; trivial.
            }
            assert (forall l, [seq omap fst match match get_access l x form_tl with
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
            do 2 rewrite HEq.
            pose (p1 := HRec form_tl l1); move:p1; move=> p1.
            case_eq (remove_option_from_list [seq omap fst (get_access l1 acc' form_tl) | acc' <- expand_access acc]).
            all: swap 1 2.
            {
                simpl; intro H.
                rewrite H in p1.
                rewrite remove_option_from_list_app2; trivial.
                destruct fold_right as [[]|]; auto.
                do 2 destruct get_access as [[]|]; auto.
                simpl in p1; discriminate p1.
            }
            move=> l1' HEq_l1.
            rewrite HEq_l1 in p1.
            destruct (get_access l1) as [[]|]; simpl in *.
            2: by discriminate.
            inversion p1 as [H]; clear p1 H l.
            pose (p2 := HRec form_tl l2); move:p2; move=> p2.
            case_eq (remove_option_from_list [seq omap fst (get_access l2 acc' form_tl) | acc' <- expand_access acc]).
            all: swap 1 2.
            {
                simpl; intro H.
                rewrite H in p2.
                rewrite remove_option_from_list_app3.
                2: rewrite remove_option_from_list_app2; trivial.
                destruct fold_right as [[]|]; auto.
                destruct get_access as [[]|]; auto.
                simpl in p2; discriminate p2.
            }
            move=> l2' HEq_l2; simpl.
            rewrite HEq_l2 in p2.
            destruct (get_access l2) as [[]|]; simpl in *.
            2: by discriminate.
            inversion p2 as [H]; clear p2 H l.
            match goal with
            | |- omap fst match match match ?f with Some _ => _ | None => _ end with Some _ => _ | None => _ end with Some _ => _ | None => _ end
                = omap flatten (remove_option_from_list (_ ++ _ ++ ?l)) =>
                    assert (omap fst f = omap flatten (remove_option_from_list l)) as HEq';
                    [> idtac | destruct f as [[]|]; simpl in * ]
            end.
            all: swap 1 2.
            {
                apply remove_option_from_list_lemma.
                by rewrite HEq_l1; auto.
                apply remove_option_from_list_lemma.
                by rewrite HEq_l2; auto.
                by assumption.
            }
            all: swap 1 2.
            {
                rewrite remove_option_from_list_app3; auto.
                rewrite remove_option_from_list_app3; auto.
                match goal with | |- ?l = _ => destruct l end; trivial.
                discriminate.
            }
            move: (HRec form_tl) split_Eq mod_Eq HEq; clear; move=> HRec split_Eq mod_Eq HEq.
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
            rewrite HEq.
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
    | ASlice iL acc => ASlice iL (add_all acc n)
    end.

Inductive well_bounded : access -> list nat -> nat -> Prop :=
    | wb_Bot : forall n l, well_bounded AAll (n::l) n
    | wb_Ind : forall acc form n ind l, well_bounded acc form n ->
        l <> 0 ->
        well_bounded (ASlice (ind::nil) acc) (l::form) n.

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

Lemma empty_disj {A : Type} (l : list A): {l = nil} + {l <> nil}.
Proof.
    destruct l; auto.
    right; discriminate.
Qed.
(* 
Theorem get_access_add_all_slice:
    forall acc form n,
        well_bounded acc form n ->
    forall iL,
        length iL = prod_list form ->
        1 < n ->
        get_access iL acc form =
        get_access iL (add_all acc n) form.
Proof.
    move=> acc; induction acc as [|iL acc HRec]; simpl.
    {
        move=> form n wellB iL; inversion wellB; simpl.
        move=> lengthEq NotZero; rewrite lengthEq.
        unfold muln, muln_rec.
        assert (n <> 0) as NotZero
        rewrite Nat.mul_comm; rewrite Nat.mod_mul; simpl; trivial.
        rewrite Nat.div_mul; trivial.
        destruct (split_into_segments_soundness _ _ _ lengthEq) as [iL' [-> [HForall [<- lengthEq']]]].
        rewrite nth_gen_list_length; trivial.
        move: NotZero; rewrite <- lengthEq'.
        rewrite len_gen_list.
        induction iL' as [|hd tl HRec]; simpl; [> by idtac | move=> _].
        case_eq (remove_option_from_list (concat tl)).
        {
            move=> tl' HEqtl.
            rewrite HEqtl in HRec.
            destruct (empty_disj tl) as [HEq|HDiff].
            {
                symmetry in HEq; destruct HEq; simpl in *.
                rewrite app_nil_r.
                destruct remove_option_from_list; trivial.
                destruct (_ =? _).
            }
            destruct fold_right as [[]|]; simpl in *.
            2: discriminate.
            inversion HRec as [H]; clear HRec; destruct H.
            case_eq (remove_option_from_list hd).
            + move=> hd' HEqHd; rewrite (remove_option_from_list_app_Some _ _ _ _ HEqHd HEqtl); trivial.
            + move=> HEqNone; rewrite remove_option_from_list_app2; trivial.
        }
        {
            move=> HEqNone; rewrite remove_option_from_list_app3; trivial.
            destruct fold_right as [[]|]; trivial.
            rewrite HEqNone in HRec; simpl in HRec.
            discriminate.
        }
    }
    {
        move=> form n wellB'; inversion wellB' as [|hd tl n' ind l wellB NotZero'].
        clear H H0 H1 H2 n' wellB' iL hd form; simpl.
        move=> iL lengthEq NotZero; rewrite lengthEq.
        destruct (_ =? _); trivial.
        unfold muln, muln_rec.
        rewrite Nat.mul_comm; rewrite Nat.div_mul; trivial.
        destruct (split_into_segments_soundness _ _ _ lengthEq) as [iL' [-> [HEq _]]].
        move: (@Forall_nth_error _ (fun l => length l = prod_list tl) ind iL').
        destruct nth_error as [l'|]; trivial.
        move=> H; specialize H with l'; move: H; impl_tac; trivial.
        impl_tac; trivial.
        move=> H.
        pose (p := HRec _ _ wellB _ H NotZero); move: p; clear.
        move=> H.
        do 2 destruct get_access as [[]|]; simpl in *; inversion H; reflexivity.
    }
Qed. *)

Theorem get_access_add_all_slice:
    forall acc form n,
        well_bounded acc form n ->
    forall iL,
        length iL = prod_list form ->
        n <> 0 ->
        omap fst (get_access iL acc form) =
        omap fst (get_access iL (add_all acc n) form).
Proof.
    move=> acc; induction acc as [|iL acc HRec]; simpl.
    {
        move=> form n wellB iL; inversion wellB; simpl.
        move=> lengthEq NotZero; rewrite lengthEq.
        unfold muln, muln_rec.
        rewrite Nat.mul_comm; rewrite Nat.mod_mul; simpl; trivial.
        rewrite Nat.div_mul; trivial.
        destruct (split_into_segments_soundness _ _ _ lengthEq) as [iL' [-> [HForall [<- lengthEq']]]].
        rewrite <- lengthEq'.
        rewrite nth_gen_list_length; trivial.
        rewrite len_gen_list.
        clear.
        induction iL' as [|hd tl HRec]; simpl; trivial.
        case_eq (remove_option_from_list (concat tl)).
        {
            move=> tl' HEqtl; rewrite HEqtl in HRec.
            destruct fold_right as [[]|]; simpl in *.
            2: discriminate.
            inversion HRec as [H]; clear HRec; destruct H.
            case_eq (remove_option_from_list hd).
            + move=> hd' HEqHd; rewrite (remove_option_from_list_app_Some _ _ _ _ HEqHd HEqtl); trivial.
            + move=> HEqNone; rewrite remove_option_from_list_app2; trivial.
        }
        {
            move=> HEqNone; rewrite remove_option_from_list_app3; trivial.
            destruct fold_right as [[]|]; trivial.
            rewrite HEqNone in HRec; simpl in HRec.
            discriminate.
        }
    }
    {
        move=> form n wellB'; inversion wellB' as [|hd tl n' ind l wellB NotZero'].
        clear H H0 H1 H2 n' wellB' iL hd form; simpl.
        move=> iL lengthEq NotZero; rewrite lengthEq.
        destruct (_ =? _); trivial.
        unfold muln, muln_rec.
        rewrite Nat.mul_comm; rewrite Nat.div_mul; trivial.
        destruct (split_into_segments_soundness _ _ _ lengthEq) as [iL' [-> [HEq _]]].
        move: (@Forall_nth_error _ (fun l => length l = prod_list tl) ind iL').
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
    | AAll => ASlice (i::nil) AAll
    | ASlice iL acc => ASlice iL (change_access i acc)
    end.

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
            | Uint _ _ (Some 0) => None
            | Uint dir m (Some _) => Some (Uint dir m None)
            | Uint dir m None => None
            | Array _ 0 => None
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

Theorem val_of_type_CoIL {A : Type} :
    forall typ cst l,
        @val_of_type A (CoIL cst) typ l ->
            l = nil /\ typ = Nat.
Proof.
    move=> typ cst; induction typ as [|d [] []|typ HRec ae]; simpl; auto.
    1-6: by move=> l [].
    move=> l H; apply HRec in H; destruct H.
    destruct l; simpl in H; by idtac.
Qed.

Theorem val_of_type_CoIR {A : Type}:
    forall typ dir iL form l,
        @val_of_type A (CoIR dir iL form) typ l ->
        length iL = prod_list form /\ prod_list form <> 0.
Proof.
    move=> typ; induction typ as [|d [m| |] n| typ HRec ae]; simpl.
    1,3,4: by move=> _ iL form _ [].
    all: move=> dir iL form l.
    {
        destruct n as [n|].
        all: move=> [-> [H [<- _]]]; auto.
    }
    {
        apply HRec.
    }
Qed.

Theorem val_of_CoIL_abs {A : Type}:
    forall acc typ z l d m n,
        @val_of_type A (CoIL z) typ l ->
        Some (Uint d m n) = get_var_type' acc (Some typ) -> False.
Proof.
    move=> acc; induction acc as [|iL acc HRec]; simpl.
    {
        move=> [|d' m' [n'|]|typ a]; simpl.
        2,3: destruct m'; do 5 intro; move=> [].
        all: do 6 intro; intro HEq; inversion HEq; discriminate.
    }
    {
        destruct iL as [|hd []].
        1,3: do 7 intro; intro Abs; inversion Abs.
        move=> [|d' m' [n'|]|typ len]; simpl.
        by do 6 intro; rewrite get_var_type'_None; discriminate.
        1,2: by destruct m'; do 5 intro; move=> [].
        destruct len.
        by rewrite get_var_type'_None; idtac.
        do 5 intro; apply HRec.
    }
Qed.

Theorem get_var_type'_wb {A : Type}:
    forall acc typ form iL d' d m n l,
        n > 1 ->
        convert_type typ = Some (d', form) ->
        @val_of_type A (CoIR d' iL (l ++ form)) typ l ->
        Some (Uint d m (Some n)) = get_var_type' acc (Some typ) ->
        well_bounded acc form n.
Proof.
    move=> acc; induction acc as [|iL acc HRec]; simpl.
    {
        move=> [|d' m' [n'|]|typ a]; simpl.
        1: do 9 intro; move=> [].
        3: do 10 intro; intro HEq; inversion HEq; discriminate.
        all: destruct m'.
        2,3,5,6: do 9 intro; move=> [].
        all: do 9 intro; move=> [EqApp H'] Hyp.
        {
            apply app_inj in EqApp; rewrite EqApp.
            inversion Hyp; constructor.
        }
        {
            inversion Hyp.
        }
    }
    {
        destruct iL as [|hd []].
        1,3: do 11 intro; intro Abs; inversion Abs.
        move=> [|d' m' [n'|]|typ len]; simpl.
        by do 9 intro; rewrite get_var_type'_None; discriminate.
        {
            destruct m'.
            2,3: do 9 intro; move=> [].
            move=> form iL d2 d m n2 l sup_1 convert [EqApp H] get_var.
            apply app_inj in EqApp; rewrite EqApp; clear EqApp.
            destruct acc as [|[|i []] acc]; simpl in *.
            all: destruct n' as [|n'].
            1-4: discriminate.
            1-2: rewrite get_var_type'_None in get_var; discriminate.
            1-2: discriminate.
        }
        {
            rewrite get_var_type'_None.
            do 8 intro; discriminate.
        }
        {
            move=> [|form_hd form_tl] iL d' d m n l; simpl.
            all: move=> Inf convert val_of get_var_type'.
            all: move: (HRec typ); clear HRec; move=> HRec.
            all: move: val_of HRec get_var_type'.
            all: destruct convert_type as [[]|]; inversion convert.
            move=> val_of HRec get_var_type'.
            destruct form_hd.
            {
                rewrite get_var_type'_None in get_var_type'; discriminate.
            }
            constructor; auto.
            refine (HRec _ _ _ _ _ _ (_ ++ [:: _ ]) _ _ _ _).
            by assumption.
            by reflexivity.
            by rewrite <-app_assoc; simpl; exact val_of.
            by exact get_var_type'.
        }
    }
Qed.

Theorem all_all_var_lemma:
    forall v acc type_ctxt ctxt d m n,
        get_var_type type_ctxt (unfold_access acc v) = Some (Uint d m n) ->
        well_typed_ctxt (imap.elements type_ctxt) ctxt ->
        n > 1 ->
        eval_var v ctxt acc =
        eval_var v ctxt (add_all acc n).
Proof.
    move=> v; induction v as [i|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl.
    {
        move=> acc type_ctxt ctxt d m n Hfind well_typed NotZero.
        case_eq (find_val ctxt i); trivial.
        move=> c find_eq.
        rewrite get_var_type_unfold in Hfind; simpl in Hfind.
        apply (well_typed_ctxt_imp_find_val _ _ i c) in well_typed; trivial.
        destruct well_typed as [typ' [Hfind' val_of]].
        assert (Some (Uint d m n) = get_var_type' acc (Some typ')) as TypeEq.
        {
            rewrite find_val_is_imap_find in Hfind.
            rewrite Hfind' in Hfind.
            auto.
        }
        clear Hfind Hfind'.
        destruct c as [z|d' iL form]; trivial.
        {
            apply (@val_of_CoIL_abs (option Z) _ _ z nil) in TypeEq; auto.
            destruct TypeEq.
        }
        pose (p := get_access_add_all_slice acc form n); move: p.
        impl_tac.
        {
            apply (get_var_type'_wb _ typ' _ iL d' d m _ nil NotZero); trivial.
            {
                apply (val_of_type_convert iL _ _ _ nil); simpl.
                assumption.
            }
            {
                destruct n; simpl in *; inversion NotZero.
            }
        }
        {
            move=> p; move: (p iL); clear p.
            impl_tac.
            {
                move: (val_of_type_convert iL typ' d' form nil); simpl.
                impl_tac; trivial.
                move=> H.
                apply (val_of_type_len _ _ _ d' _ form) in val_of; trivial.
                destruct val_of as [_ <-]; simpl; trivial.
            }
            impl_tac.
            {
                destruct n; simpl in *.
                2: discriminate.
                inversion NotZero.
            }
            do 2 destruct get_access as [[]|]; simpl.
            + move=> H; inversion H; admit.
            + discriminate.
            + discriminate.
            + reflexivity.
        }
    }
    {
        admit.
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


Theorem expand_var_lemma:
    forall v acc type_ctxt ctxt d m n,
        get_var_type type_ctxt (unfold_access acc v) = Some (Uint d m (Some n)) ->
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
                3: rewrite get_var_type'_None in H.
                all: by discriminate.
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
        move=> acc type_ctxt ctxt d m n.
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
        destruct (get_var_type) as [[|dir m []|t len]|].
        1,3,5: by discriminate.
        all: move=> HEq.
        + destruct n; [> discriminate | inversion HEq ]; constructor.
        + specialize HRec with (Array t len); move: HRec; impl_tac; trivial.
            destruct len; [> discriminate | inversion HEq ].
            move=> HRec; inversion HRec; trivial.
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
        destruct n as [[|n]|]; simpl.
        {
            move=> v valid _ get_type.
            exfalso.
            apply get_var_imp_valid in get_type; trivial.
            inversion get_type.
            auto.
        }
        all: admit.
        (* destruct n as [|n]; simpl.
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
        exact (Nat2Z.is_nonneg _). *)
    }
    {
        admit.
    }
Admitted.
