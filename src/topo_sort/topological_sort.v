Require Import List.
Require Import PeanoNat.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils list_relations coq_missing_lemmas.

Fixpoint gen_list {A} (v : A) (len : nat) : seq A :=
    match len with
    | 0 => nil
    | S len => v :: gen_list v len
    end.

Fixpoint update_list {A} (el : A) (l : seq A) (pos : nat) : seq A :=
    match l with
    | nil => nil
    | hd :: tl =>
        match pos with
        | 0 => el :: tl
        | S pos' => hd :: update_list el tl pos'
        end
    end.

Fixpoint find_parents (f : nat -> nat -> bool) (current_scan : nat) (pos : nat) (indices : list (option nat))
    (visited : list bool) (len : nat) (fuel : nat)
    : option (nat * list (option nat)) :=
    match fuel with
    | 0 => None
    | S fuel =>
        match current_scan with
        | 0 => Some (0, indices)
        | S current_scan =>
            match find_parents f current_scan pos indices visited len fuel with
            | None => None
            | Some (above, indices) =>
                if f current_scan pos
                then
                    match visit f current_scan indices visited len fuel with
                    | Some (depth, indices) => Some (Nat.max above depth, indices)
                    | None => None
                    end
                else Some (above, indices)
            end
        end
    end
with visit (f : nat -> nat -> bool) (pos : nat) (indices : list (option nat)) (visited : list bool) (len : nat)
    (fuel : nat)
    : option (nat * list (option nat)) :=
    match fuel with
    | 0 => None
    | S fuel =>
        if Bool.eqb (nth true visited pos) true
        then
            None
        else
            match nth_error indices pos with
            | None => None
            | Some (Some depth) => Some (depth, indices)
            | Some None =>
                    let visited := update_list true visited pos in
                match find_parents f len pos indices visited len fuel with
                | Some (depth, indices) => Some (depth.+1, update_list (Some depth.+1) indices pos)
                | None => None
                end
            end
    end.

Fixpoint visit_all (f : nat -> nat -> bool) (pos : nat) (indices : list (option nat))
    (visited : list bool) (len : nat) (fuel : nat) : option (list (option nat)) :=
    match pos with
    | 0 => Some indices
    | S pos =>
        match visit f pos indices visited len fuel with
        | None => None
        | Some (_, indices') =>
            visit_all f pos indices' visited len fuel
        end
    end.

Fixpoint remove_option_from_list {A : Type} (l : list (option A)) : option (list A) :=
    match l with
    | nil => Some nil
    | hd::tl =>
        match hd with
        | None => None
        | Some hd' =>
            match remove_option_from_list tl with
            | None => None
            | Some tl' => Some (hd'::tl')
            end
        end
    end.

Definition build_order (f : nat -> nat -> bool) (len : nat) : option (seq nat) :=
    match visit_all f len (gen_list None len) (gen_list false len) len ((len + 1) * (len + 1)) with
    | None => None
    | Some indices => remove_option_from_list indices
    end.
    

Lemma find_parents_ind:
    forall max_fuel f,
        (forall fuel pos visited indices indices' depth,
            fuel <= max_fuel ->
            pos < length indices ->
            visit f pos indices visited (length indices) fuel = Some (depth, indices') ->
            length visited = length indices ->
            (forall in1 in2 out1 out2,
                nth_error indices in1 = Some (Some out1) ->
                nth_error indices in2 = Some (Some out2) ->
                f in1 in2 -> out1 < out2) ->
            (forall i1 i2 o1,
                nth_error indices i1 = Some (Some o1) ->
                f i2 i1 -> i2 < length indices ->
                exists o2, nth_error indices i2 = Some (Some o2)) ->
            nth_error indices' pos = Some (Some depth) /\
            list_rel (fun o1 o2 => match o1 with None => True | Some _ => o1 = o2 end) indices indices' /\
            (forall i1 i2 o1,
                nth_error indices' i1 = Some (Some o1) ->
                f i2 i1 -> i2 < length indices ->
                exists o2, nth_error indices' i2 = Some (Some o2)) /\
            (forall i,
                nth true visited i = true -> nth_error indices i = nth_error indices' i) /\
            forall in1 in2 out1 out2,
                nth_error indices' in1 = Some (Some out1) ->
                nth_error indices' in2 = Some (Some out2) ->
                f in1 in2 -> out1 < out2) ->
        forall fuel pos indices visited current_pos indices' depth,
            fuel <= max_fuel ->
            current_pos <= length indices ->
            find_parents f current_pos pos indices visited (length indices) fuel = Some (depth, indices') ->
            length visited = length indices ->
            (forall in1 in2 out1 out2,
                nth_error indices in1 = Some (Some out1) ->
                nth_error indices in2 = Some (Some out2) ->
                f in1 in2 -> out1 < out2) ->
            (forall i1 i2 o1,
                nth_error indices i1 = Some (Some o1) ->
                f i2 i1 -> i2 < length indices ->
                exists o2, nth_error indices i2 = Some (Some o2)) ->
            list_rel (fun o1 o2 => match o1 with None => True | Some _ => o1 = o2 end) indices indices' /\
            (forall i1 i2 o1,
                nth_error indices' i1 = Some (Some o1) ->
                f i2 i1 -> i2 < length indices ->
                exists o2, nth_error indices' i2 = Some (Some o2)) /\
            (forall i,
                nth true visited i = true -> nth_error indices i = nth_error indices' i) /\
            (forall in1 in2 out1 out2,
                nth_error indices' in1 = Some (Some out1) ->
                nth_error indices' in2 = Some (Some out2) ->
                f in1 in2 -> out1 < out2) /\
            (forall i, f i pos -> i < current_pos ->
                exists depth',
                    nth_error indices' i = Some (Some depth') /\ depth' <= depth).
Proof.
    move=> max_fuel f HRec_visit fuel pos indices visited.
    induction fuel as [|fuel HRec_fuel]; simpl; [> discriminate | idtac ].
    move=> [|current_pos] indices' depth SInf_fuel.
    {
        move=> _ H; inversion H as [[H1 H2]].
        destruct H1; destruct H2; clear H.
        intros.
        split.
        by clear; induction indices as [|[]]; constructor; trivial.
        split; [> assumption | idtac ].
        split; [> reflexivity | idtac ].
        by split; [> assumption | idtac ].
    }
    move: (HRec_fuel current_pos); clear HRec_fuel; move=> HRec_fuel.
    destruct find_parents as [[depth_out indices_out]|]; [> idtac | discriminate ].
    move=> SInf_cpos H length_eq in_soundness all_sons_defined.
    move: (HRec_fuel indices_out depth_out).
    impl_tac; [> by auto | idtac ].
    impl_tac; [> by auto | idtac ].
    impl_tac; [> reflexivity | idtac ].
    impl_tac; [> assumption | idtac ].
    impl_tac; [> assumption | idtac ].
    impl_tac; [> assumption | idtac ].
    move=> [indices_soundness [all_sons_defined' [respects_visited [out1_soundness partial_soundness]]]].
    move: H; case_eq (f current_pos pos); move=> f_eq.
    {
        move: (HRec_visit fuel current_pos visited indices_out); clear HRec_visit.
        rewrite <-(list_rel_length _ _ _ indices_soundness).
        destruct visit as [[depth_visit indices_visit]|]; [> idtac | discriminate ].
        move=> H; move: (H indices_visit depth_visit); clear H.
        impl_tac; [> by auto | idtac ].
        impl_tac; [> assumption | idtac ].
        impl_tac; [> reflexivity | idtac ].
        impl_tac; [> assumption | idtac ].
        impl_tac; [> assumption | idtac ].
        impl_tac; [> assumption | idtac ].
        move=> [nth_eq [indices_visit_preserved [all_sons_defined2 [respects_visited' out2_soundness]]]].
        move=> H; inversion H as [[H1 H2]].
        destruct H1; destruct H2; clear H.
        split.
        {
            refine (list_rel_trans _ _ _ _ indices_soundness indices_visit_preserved).
            move=> [x|]; [> idtac | by constructor ].
            move=> y z <-; trivial.
        }
        split; [> assumption | idtac ].
        split.
        {
            move=> i nth_visited_eq.
            rewrite respects_visited; trivial.
            apply respects_visited'; trivial.
        }
        split; [> assumption | idtac ].
        move=> i f_eq' SInf.
        destruct (leq_Cases _ _ SInf) as [HEq|SInf'].
        {
            inversion HEq as [HEq']; destruct HEq'; clear HEq.
            rewrite nth_eq; eexists; split; [> reflexivity | idtac ].
            apply/leP.
            exact (Nat.le_max_r _ _ ).
        }
        {
            apply partial_soundness in f_eq'; [> idtac | by auto ].
            destruct f_eq' as [depth' [nth_eq' inf]].
            exists depth'.
            split.
            {
                move: indices_visit_preserved nth_eq'; clear.
                move=> lr; move: i.
                induction lr as [|h1 h2 t1 t2 rel_hd rel_tl HRec].
                all: move=> [|i]; simpl.
                1,2: by discriminate.
                2: by exact (HRec i).
                move=> H; inversion H as [H']; clear H.
                symmetry in H'; destruct H'.
                destruct rel_hd; reflexivity.
            }
            {
                apply/leP.
                refine (Nat.le_trans _ _ _ (Nat.le_max_l _ _) (Nat.max_le_compat_r _ _ _ _)).
                apply/leP; assumption.
            }
        }
    }
    {
        move=> H; inversion H as [[H1 H2]]; clear H.
        destruct H1; destruct H2.
        do 4 (split; [> assumption | idtac ]).
        move=> i f_eq' SInf.
        destruct (leq_Cases _ _ SInf) as [HEq|SInf'].
        {
            inversion HEq as [HEq']; clear HEq; destruct HEq'.
            rewrite f_eq in f_eq'; discriminate.
        }
        {
            apply partial_soundness; auto.
        }
    }
Qed.

Lemma nth_error_update_list {A}:
    forall el l pos1 pos2,
        pos1 < length l ->
            nth_error (@update_list A el l pos1) pos2 =
                if pos1 =? pos2
                then Some el
                else
                    nth_error l pos2.
Proof.
    move=> el l.
    induction l as [|hd tl HRec]; move=> [|pos1]; simpl.
    1,2: by auto.
    all: move=> [|pos2]; simpl.
    1-3: by reflexivity.
    intro; apply HRec; auto.
Qed.

Lemma nth_update_list {A}:
    forall default el l pos1 pos2,
        pos1 < length l ->
            nth default (@update_list A el l pos1) pos2 =
                if pos1 =? pos2
                then el
                else
                    nth default l pos2.
Proof.
    move=> default el l.
    induction l as [|hd tl HRec]; move=> [|pos1]; simpl.
    1,2: by auto.
    all: move=> [|pos2]; simpl.
    1-3: by reflexivity.
    intro; apply HRec; auto.
Qed.

Lemma length_update_list {A}:
    forall el l pos,
        length (@update_list A el l pos) = length l.
Proof.
    move=> el l; induction l as [|hd tl HRec]; move=> [|pos]; simpl; auto.
Qed.

Lemma find_parents_not_pos:
    forall f fuel current_pos pos visited indices,
        pos < length indices ->
        length visited = length indices ->
        f pos pos = true ->
        pos < current_pos ->
        find_parents f current_pos pos indices (update_list true visited pos) (length indices) fuel = None.
Proof.
    move=> f fuel current_pos pos visited indices pos_inf_length length_eq f_eq_true.
    move: current_pos; induction fuel as [|fuel HRec]; simpl.
    by reflexivity.
    move=> [|c_pos]; [> by auto | idtac ].
    specialize HRec with c_pos.
    move=> H; destruct (leq_Cases _ _ H) as [HEq|SInf]; clear H.
    {
        inversion HEq as [H']; clear HEq; destruct H'.
        destruct find_parents as [[]|]; [> idtac | reflexivity ].
        rewrite f_eq_true.
        destruct fuel; simpl; [> reflexivity | idtac ].
        assert (nth true (update_list true visited pos) pos = true) as ->.
        2: by simpl; reflexivity.
        rewrite <-length_eq in pos_inf_length; move: pos_inf_length.
        clear.
        move: pos; induction visited as [|hd tl HRec]; move=> [|pos]; simpl; trivial.
        intro; apply HRec; auto.
    }
    {
        rewrite HRec; trivial.
    }
Qed.

Lemma visit_soundness:
    forall max_fuel f fuel pos visited indices indices' depth,
        fuel <= max_fuel ->
        pos < (length indices) ->
        visit f pos indices visited (length indices) fuel = Some (depth, indices') ->
        length visited = length indices ->
        (forall in1 in2 out1 out2,
            nth_error indices in1 = Some (Some out1) ->
            nth_error indices in2 = Some (Some out2) ->
            f in1 in2 -> out1 < out2) ->
        (forall i1 i2 o1,
            nth_error indices i1 = Some (Some o1) ->
            f i2 i1 -> i2 < length indices ->
            exists o2, nth_error indices i2 = Some (Some o2)) ->
        nth_error indices' pos = Some (Some depth) /\
        list_rel (fun o1 o2 => match o1 with None => True | Some _ => o1 = o2 end) indices indices' /\
        (forall i1 i2 o1,
            nth_error indices' i1 = Some (Some o1) ->
            f i2 i1 -> i2 < length indices ->
            exists o2, nth_error indices' i2 = Some (Some o2)) /\
        (forall i,
            nth true visited i = true -> nth_error indices i = nth_error indices' i) /\
        (forall in1 in2 out1 out2,
            nth_error indices' in1 = Some (Some out1) ->
            nth_error indices' in2 = Some (Some out2) ->
            f in1 in2 -> out1 < out2).
Proof.
    move=> max_fuel f; induction max_fuel as [|max_fuel HRec].
    by move=> [|fuel]; simpl; [> discriminate | auto ].
    move=> [|fuel]; simpl; [> by discriminate | idtac ].
    move=> pos visited indices indices' depth SInf.
    case_eq (Bool.eqb (nth true visited pos) true); [> discriminate | move=> bool_eq_false ].
    case_eq (nth_error indices pos); [> idtac | by discriminate ].
    move=> [depth'|].
    {
        move=> HEq SInf_pos H; inversion H as [[H1 H2]].
        destruct H1; destruct H2; clear H.
        intros.
        split; [> assumption | idtac ].
        split.
        by clear; induction indices as [|[]]; constructor; trivial.
        split; [> assumption | idtac ].
        split; [> reflexivity | assumption ].
    }
    {
        move=> nth_None.
        move=> SInf_pos find_parents_eq length_eq in_soundness all_sons_defined; move: find_parents_eq.
        move: (find_parents_ind max_fuel f HRec fuel pos indices (update_list true visited pos) (length indices)).
        move: (find_parents_not_pos f fuel (length indices) pos visited indices SInf_pos length_eq); move=> f_pos_pos_false.
        clear HRec.
        destruct find_parents as [[depth_fp indices_fp]|]; [> idtac | discriminate ].
        move=> H; move: (H indices_fp depth_fp); clear H.
        impl_tac; [> by auto | idtac ].
        impl_tac; [> by trivial | idtac ].
        impl_tac; [> reflexivity | idtac ].
        impl_tac; [> rewrite length_update_list; assumption | idtac ].
        impl_tac; [> assumption | idtac ].
        impl_tac; [> assumption | idtac ].
        move=> [indices_preserved [all_sons_defined' [respects_visited [out_soundness partial_soundness]]]].
        move=> H; inversion H as [[H1 H2]]; clear H.
        destruct H1; destruct H2.
        rewrite (list_rel_length _ _ _ indices_preserved) in SInf_pos.
        split.
        {
            rewrite nth_error_update_list.
            by rewrite Nat.eqb_refl; reflexivity.
            by assumption.
        }
        split.
        {
            move: indices_preserved nth_None; clear.
            move=> lr; move: pos.
            induction lr as [|h1 h2 t1 t2 rel_hd rel_tl]; move=> [|pos]; simpl.
            1,2: discriminate.
            by move=> HEq; inversion HEq; constructor; trivial.
            by constructor; auto.
        }
        split.
        {
            move=> i1 i2.
            rewrite nth_error_update_list; [> idtac | assumption ].
            rewrite nth_error_update_list; [> idtac | assumption ].
            case_eq (pos =? i1); case_eq (pos =? i2).
            {
                do 2 rewrite Nat.eqb_eq.
                do 2 (move=> H; destruct H).
                unfold is_true; move=> o1 _ f_eq.
                rewrite <-(list_rel_length _ _ _ indices_preserved) in SInf_pos.
                discriminate f_pos_pos_false; assumption.
            }
            {
                rewrite Nat.eqb_eq.
                move=> _ H o1 _ f_eq i2_inf; destruct H.
                destruct (partial_soundness _ f_eq i2_inf) as [depth [-> _]].
                eauto.
            }
            {
                intros; eauto.
            }
            {
                move=> _ _; apply all_sons_defined'.
            }
        }
        split.
        {
            move=> i nth_visited_eq.
            rewrite nth_error_update_list; trivial.
            case_eq (pos =? i).
            {
                rewrite Nat.eqb_eq; move=> H; destruct H.
                rewrite nth_visited_eq in bool_eq_false; simpl in bool_eq_false; discriminate.
            }
            {
                move=> pos_diff; apply respects_visited.
                rewrite <-(list_rel_length _ _ _ indices_preserved) in SInf_pos.
                rewrite <-length_eq in SInf_pos.
                rewrite nth_update_list; trivial.
                rewrite pos_diff; assumption.
            }
        }
        {
            move=> in1 in2 out1 out2.
            rewrite nth_error_update_list; [> idtac | assumption ].
            rewrite nth_error_update_list; [> idtac | assumption ].
            case_eq (pos =? in1); case_eq (pos =? in2).
            {
                do 2 rewrite Nat.eqb_eq.
                do 2 (move=> H; destruct H).
                unfold is_true; move=> _ _ f_eq.
                rewrite <-(list_rel_length _ _ _ indices_preserved) in SInf_pos.
                discriminate f_pos_pos_false; assumption.
            }
            {
                rewrite Nat.eqb_eq.
                move=> _ H HEq nth_eq f_eq; destruct H.
                inversion HEq as [H]; clear HEq; destruct H.
                specialize all_sons_defined' with in2 pos out2; move: all_sons_defined'.
                rewrite (list_rel_length _ _ _ indices_preserved).
                do 3 (impl_tac; [> assumption | idtac ]).
                move=> [out_pos nth_eq'].
                rewrite <- respects_visited in nth_eq'.
                by rewrite nth_None in nth_eq'; discriminate.
                rewrite <-(list_rel_length _ _ _ indices_preserved) in SInf_pos.
                rewrite <-length_eq in SInf_pos.
                rewrite nth_update_list; trivial.
                rewrite Nat.eqb_refl; reflexivity.
            }
            {
                rewrite Nat.eqb_eq.
                move=> H _ nth_eq HEq f_eq; destruct H.
                inversion HEq as [H]; clear HEq; destruct H.
                destruct (partial_soundness _ f_eq) as [depth' [nth_eq' HInf]].
                {
                    rewrite (list_rel_length _ _ _ indices_preserved).
                    apply/ltP.
                    rewrite <-nth_error_Some; rewrite nth_eq; discriminate.
                }
                rewrite nth_eq' in nth_eq.
                inversion nth_eq as [H]; clear nth_eq; destruct H.
                auto.
            }
            {
                move=> _ _; apply out_soundness.
            }
        }
    }
Qed.

Lemma visit_all_soundness:
    forall f fuel visited pos indices indices',
        visit_all f pos indices visited (length indices) fuel = Some indices' ->
        length visited = length indices ->
        (forall i1 i2 o1,
            nth_error indices i1 = Some (Some o1) ->
            f i2 i1 -> i2 < length indices ->
            exists o2, nth_error indices i2 = Some (Some o2)) ->
        (forall in1 in2 out1 out2,
            nth_error indices in1 = Some (Some out1) ->
            nth_error indices in2 = Some (Some out2) ->
            f in1 in2 -> out1 < out2) ->
        pos <= length indices ->
        list_rel (fun o1 o2 => match o1 with None => True | Some _ => o1 = o2 end) indices indices' /\
        (forall i1 i2 o1,
            nth_error indices' i1 = Some (Some o1) ->
            f i2 i1 -> i2 < length indices' ->
            exists o2, nth_error indices' i2 = Some (Some o2)) /\
        (forall in1 in2 out1 out2,
            nth_error indices' in1 = Some (Some out1) ->
            nth_error indices' in2 = Some (Some out2) ->
            f in1 in2 -> out1 < out2).
Proof.
    move=> f fuel visited pos.
    induction pos as [|pos HRec]; simpl.
    {
        move=> indices indices' H; inversion H as [H']; clear H; destruct H'.
        intros.
        split.
        by clear; induction indices as [|[]]; constructor; trivial.
        split; assumption.
    }
    {
        move=> indices indices2 eval_eq length_eq all_sons_defined graph_soundness pos_inf.
        move: (visit_soundness fuel f fuel pos visited indices) eval_eq.
        destruct visit as [[depth indices1]|].
        2: by discriminate.
        move=> H; move: (H indices1 depth); clear H.
        impl_tac; [> by trivial | idtac ].
        impl_tac; [> assumption | idtac ].
        impl_tac; [> reflexivity | idtac ].
        do 3 (impl_tac; [> assumption | idtac ]).
        move=> [_ [lrel [all_sons_defined' [_ graph_soundness']]]] visit_all_eq.
        rewrite (list_rel_length _ _ _ lrel) in visit_all_eq.
        apply HRec in visit_all_eq; trivial.
        2-4: by rewrite <-(list_rel_length _ _ _ lrel); auto.
        destruct visit_all_eq as [lrel' [all_sons_defined'' graph_soundness'']].
        split; [> idtac | split; assumption ].
        refine (list_rel_trans _ _ _ _ lrel lrel').
        move=> [x|]; [> idtac | by constructor ].
        move=> y z <-; trivial.
    }
Qed.

Lemma length_gen_list {A}:
    forall el l,
        length (@gen_list A el l) = l.
Proof.
    move=> el l; induction l as [|l HRec]; simpl; auto.
Qed.

Lemma nth_error_genlist {A}:
    forall el l pos,
        pos < l ->
        nth_error (@gen_list A el l) pos = Some el.
Proof.
    by move=> el l; induction l as [|l HRec]; move=> [|pos]; simpl; auto.
Qed.

Lemma remove_option_from_list_soundness {A}:
    forall l_in l_out,
        @remove_option_from_list A l_in = Some l_out -> map Some l_out = l_in.
Proof.
    move=> l_in; induction l_in as [|[hd|] tl HRec]; simpl.
    by move=> l_out H; inversion H; auto.
    {
        move=> l_out; destruct remove_option_from_list; [> idtac | discriminate ].
        move=> H; inversion H; simpl; f_equal.
        apply HRec; reflexivity.
    }
    {
        discriminate.
    }
Qed.

Theorem build_order_soundness:
    forall f l ord,
        build_order f l = Some ord ->
        length ord = l /\
        forall in1 in2 out1 out2,
            nth_error ord in1 = Some out1 ->
            nth_error ord in2 = Some out2 ->
            f in1 in2 -> out1 < out2.
Proof.
    move=> f l ord.
    unfold build_order.
    move: (visit_all_soundness f ((l + 1) * (l + 1)) (gen_list false l) l (gen_list None l)).
    rewrite length_gen_list.
    destruct visit_all; [> idtac | discriminate ].
    move=> H; move: (H _ Logic.eq_refl); clear H.
    rewrite length_gen_list.
    impl_tac; [> reflexivity | idtac ].
    impl_tac.
    {
        move=> i1 i2 o1 nth_eq.
        assert (i1 < l).
        {
            apply/ltP.
            rewrite <-(length_gen_list (@None nat)).
            rewrite <-nth_error_Some; rewrite nth_eq.
            discriminate.
        }
        rewrite nth_error_genlist in nth_eq; trivial.
        by discriminate.
    }
    impl_tac.
    {
        move=> i1 i2 o1 o2 nth_eq.
        assert (i1 < l).
        {
            apply/ltP.
            rewrite <-(length_gen_list (@None nat)).
            rewrite <-nth_error_Some; rewrite nth_eq.
            discriminate.
        }
        rewrite nth_error_genlist in nth_eq; trivial.
        by discriminate.
    }
    impl_tac; [> by trivial | idtac ].
    move=> [lrel [_ H]] remove_opt.
    apply remove_option_from_list_soundness in remove_opt.
    destruct remove_opt.
    apply list_rel_length in lrel.
    rewrite length_gen_list in lrel; rewrite lrel.
    rewrite map_length.
    split; [> reflexivity | idtac ].
    move=> in1 in2 out1 out2 nth_eq1 nth_eq2; apply H.
    all: rewrite nth_error_map; [> rewrite nth_eq1 | rewrite nth_eq2 ]; simpl; reflexivity.
Qed.