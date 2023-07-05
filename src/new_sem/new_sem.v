Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST usuba_ASTProp arch
    list_relations termination_funs termination_properties
    semantic_base semantic_base_proofs
    topological_sort
    def_tree_proofs use_tree_proofs build_rel_fun_proofs.

Lemma build_definitions_inner_soundness:
    forall eqns tctxt eqns_hd defs uses,
        distinct (map fst tctxt) ->
        build_definitions_inner (length eqns_hd) tctxt eqns = Some (defs, uses) ->
        map fst tctxt = map fst defs /\
        map fst tctxt = map fst uses /\
        list_rel def_tree_of_type (map snd defs) (map snd tctxt) /\
        Forall (fun p : list var * expr => let (vars, expr) := p in
            Forall (valid_var_dtree defs) vars /\
            forall v, Ensembles.In _ (expr_freefullvars expr) v -> valid_var_utree uses v) eqns /\
        Forall (fun p : list var * expr => let (vars, expr) := p in
            Forall (valid_var tctxt) vars /\
            forall v, Ensembles.In _ (expr_freefullvars expr) v -> valid_var tctxt v) eqns /\
        Forall (fun p : ident * def_tree int_or_awaits => let (v, t) := p in
            partial_valid_def_tree (length eqns_hd) v t nil (eqns_hd ++ eqns)) defs /\
        list_rel use_tree_of_type (map snd uses) (map snd tctxt) /\
        Forall (fun p : ident * use_tree => let (v, t) := p in
            partial_valid_use_tree (length eqns_hd) v t nil (eqns_hd ++ eqns)) uses.
Proof.
    move=> eqns tctxt; induction eqns as [|[vars expr] tl HRec]; simpl.
    {
        move=> eqns_hd defs uses is_map H; move: is_map.
        inversion H; clear; simpl.
        move=> is_map; repeat split.
        {
            clear is_map.
            induction tctxt as [|[i val] tl HRec]; simpl; [> reflexivity | f_equal; trivial ].
        }
        {
            clear is_map.
            induction tctxt as [|[i val] tl HRec]; simpl; [> reflexivity | f_equal; trivial ].
        }
        {
            clear.
            induction tctxt as [|[i val] tl HRec]; simpl; constructor; simpl; auto.
        }
        {
            constructor.
        }
        {
            constructor.
        }
        {
            clear; induction tctxt as [|[v t] tl HRec]; simpl.
            all: constructor; [> simpl | assumption ].
            clear; move=> pos l' top_eq HInf.
            unfold defined_in; rewrite nth_error_app2; [> idtac | apply/leP; assumption ].
            destruct (_ - _)%coq_nat; simpl.
            all: move=> [vL [e [ind [H _]]]]; inversion H.
        }
        {
            clear; induction tctxt as [|[v t] tl HRec]; simpl.
            all: constructor; [> simpl; reflexivity | assumption ].
        }
        {
            clear; induction tctxt as [|[v t] tl HRec]; simpl.
            all: constructor; [> simpl | assumption ].
            move=> pos l'; split.
            by move=> [[] _].
            move=> [HInf used_in]; move: used_in.
            unfold used_in; rewrite nth_error_app2; [> idtac | apply/leP; assumption ].
            destruct (_ - _)%coq_nat; simpl.
            all: move=> [vL [e [ind [H _]]]]; inversion H.
        }
    }
    {
        move=> eqns_hd.
        move: (HRec (eqns_hd ++ [:: (vars, expr)])).
        rewrite app_length; simpl; clear.
        rewrite Nat.add_1_r; destruct build_definitions_inner as [[defs' uses']|].
        2: by idtac.
        move=> HRec defs uses Hdistinct.
        move: (HRec defs' uses'); clear HRec.
        impl_tac; trivial.
        impl_tac; trivial.
        rewrite <-app_assoc; simpl.
        move=> [HEq1 [HEq2 [type_soundness1 [all_acc_valid [all_acc_valid' [imp_partial_valid1 [type_soundness2 imp_partial_valid2]]]]]]] full_eq.
        case_eq (update_vars vars (length eqns_hd) defs').
        2: by move=> HEq; rewrite HEq in full_eq.
        move=> defs'' update_v_eq; rewrite update_v_eq in full_eq.
        move: (update_vars_soundness tctxt _ nil _ tl expr _ _ update_v_eq).
        rewrite <-HEq1; simpl.
        impl_tac; trivial.
        impl_tac; trivial.
        impl_tac; trivial.
        impl_tac.
        {
            move=> v t HIn.
            rewrite Forall_forall in imp_partial_valid1.
            apply imp_partial_valid1 in HIn.
            rewrite add0n; rewrite addn1.
            apply partial_valid_def_tree_add_prim; assumption.
        }
        move=> [allValid1 [sub_dtree1 [HEq1' [type_soundness1' imp_valid1]]]].
        case_eq (update_expr expr (length eqns_hd) uses').
        2: by move=> HEq; rewrite HEq in full_eq.
        move=> uses'' update_e_eq; rewrite update_e_eq in full_eq.
        move: (update_expr_soundness tctxt expr _ _ tl vars nil _ _ update_e_eq).
        rewrite <-HEq2; simpl.
        impl_tac; [> refine (is_subexpr_refl _) | idtac ].
        do 3 (impl_tac; trivial).
        impl_tac.
        {
            rewrite Forall_forall in imp_partial_valid2; rewrite Forall_forall.
            move=> [v t] HIn; apply imp_partial_valid2 in HIn.
            move: HIn; clear.
            apply partial_valid_use_tree_add_prim.
        }
        move=> [acc_valid2 [type_soundness2' [HEq2' [subs2 imp_valid2]]]].
        inversion full_eq as [[Eq1 Eq2]]; destruct Eq1; destruct Eq2.
        repeat split; trivial.
        {
            constructor; auto.
            rewrite HEq1 in HEq1'; rewrite HEq2 in HEq2'.
            move: HEq1' HEq2' sub_dtree1 subs2 all_acc_valid; clear.
            move=> eq1 eq2 sub_dtree sub_utree all_acc_valid.
            rewrite Forall_forall; rewrite Forall_forall in all_acc_valid.
            move=> [vars expr] LIn; apply all_acc_valid in LIn; clear all_acc_valid.
            destruct LIn as [forall_vars forall_in_expr]; split.
            {
                rewrite Forall_forall; rewrite Forall_forall in forall_vars.
                move=> var LIn; apply forall_vars in LIn.
                move: eq1 LIn sub_dtree; clear.
                unfold valid_var_dtree.
                destruct var as [v|[v|] ind].
                3: by move=> _ [].
                all: move: defs''; induction defs' as [|[vdef def_hd] def_tl HRec].
                all: move=> [|[vdef' def_hd'] def_tl']; simpl.
                all: move=> H; inversion H; trivial.
                all: destruct ident_beq; simpl.
                by intros; discriminate.
                by move=> find_val lrel; inversion lrel; auto.
                {
                    move=> valid lrel; inversion lrel.
                    apply (sub_dtree_keep_access _ _ _ valid); assumption.
                }
                {
                    move=> valid_find lrel; inversion lrel; auto.
                    refine (HRec _ _ valid_find _); assumption.
                }
            }
            {
                move=> var In; move: (forall_in_expr _ In).
                clear In forall_in_expr forall_vars eq1 sub_dtree defs'' defs' tl expr vars.
                unfold valid_var_utree.
                destruct var as [v|[v|] ind]; trivial.
                all: move: uses'' eq2 sub_utree.
                all: induction uses' as [|[vuses use_hd] use_tl HRec].
                all: move=> [|[vuses' use_hd'] use_tl']; simpl.
                all: move=> H; inversion H; trivial.
                all: move=> lrel; inversion lrel.
                all: destruct ident_beq.
                by discriminate.
                1,3: by apply HRec; assumption.
                by move=> valid; apply (sub_utree_keep_access _ _ _ valid); assumption.
            }
        }
        {
            constructor; auto.
            split.
            {
                rewrite Forall_forall in allValid1; rewrite Forall_forall.
                move=> var LIn; apply allValid1 in LIn.
                move: LIn HEq1' type_soundness1'.
                clear; move: tctxt.
                unfold valid_var_dtree, valid_var.
                destruct var as [v|[v|]ind].
                3: move=> tctxt [].
                all: induction defs'' as [|[k1 v1] t1 HRec]; simpl.
                by move=> tctxt H; destruct (H Logic.eq_refl).
                2: by move=> tctxt [].
                all: move=> [|[k2 v2] t2] find_eq HEq; simpl in *.
                all: move: find_eq; inversion HEq.
                all: destruct ident_beq.
                by discriminate.
                by move=> find_eq lr; inversion lr; apply HRec; assumption.
                {
                    move=> find_eq lr; inversion lr.
                    refine (valid_access_keep_dtree _ _ _ find_eq _); assumption.
                }
                by move=> find_eq lr; inversion lr; apply HRec; assumption.
            }
            {
                move=> var LIn; apply acc_valid2 in LIn.
                move: LIn HEq2' type_soundness2'.
                clear; move: tctxt.
                unfold valid_var_utree, valid_var.
                destruct var as [v|[v|]ind].
                3: move=> tctxt [].
                all: induction uses'' as [|[k1 v1] t1 HRec]; simpl.
                by move=> tctxt H; destruct (H Logic.eq_refl).
                2: by move=> tctxt [].
                all: move=> [|[k2 v2] t2] find_eq HEq; simpl in *.
                all: move: find_eq; inversion HEq.
                all: rewrite ident_beq_sym; destruct ident_beq.
                by discriminate.
                by move=> find_eq lr; inversion lr; apply HRec; assumption.
                {
                    move=> find_eq lr; inversion lr.
                    refine (valid_access_keep_utree _ _ _ find_eq _); assumption.
                }
                by move=> find_eq lr; inversion lr; apply HRec; assumption.
            }
        }
        {
            rewrite Forall_forall; rewrite Forall_forall in imp_valid1.
            move=> [v t] HIn.
            apply imp_valid1 in HIn; move: HIn.
            apply partial_valid_def_tree_remove_prim.
        }
        {
            rewrite Forall_forall; rewrite Forall_forall in imp_valid2.
            move=> [v t] HIn.
            apply imp_valid2 in HIn; move: HIn.
            apply partial_valid_use_tree_remove_prim.
        }
    }
Qed.

Theorem build_definitions_soundness:
    forall tctxt eqns defs uses,
        distinct (map fst tctxt) ->
        build_definitions tctxt eqns = Some (defs, uses) ->
        map fst tctxt = map fst defs /\
        map fst tctxt = map fst uses /\
        list_rel (fun def typ =>
            match def with
            | Some def => def_tree_of_type' def typ
            | None => True end) (map snd defs) (map snd tctxt) /\
        list_rel use_tree_of_type (map snd uses) (map snd tctxt) /\
        Forall (fun p : list var * expr => let (vars, expr) := p in
            Forall (valid_var tctxt) vars /\
            forall v, Ensembles.In _ (expr_freefullvars expr) v -> valid_var tctxt v) eqns /\
        Forall (fun p : list var * expr => let (vars, expr) := p in
            Forall (valid_var_dtree' defs) vars /\
            forall v, Ensembles.In _ (expr_freefullvars expr) v -> valid_var_utree uses v) eqns /\
        Forall (fun p : ident * option (def_tree nat) => let (v, t) := p in match t with
            | None => forall pos path_in, defined_in v path_in pos eqns -> False
            | Some t => valid_def_tree v t nil eqns
            end) defs /\
        Forall (fun p : ident * use_tree =>
            let (v, t) := p in valid_use_tree v t nil eqns) uses.
Proof.
    move=> tctxt eqns defs uses.
    move :(build_definitions_inner_soundness eqns tctxt nil).
    unfold build_definitions; simpl.
    destruct build_definitions_inner as [[defs' uses']|].
    2: by idtac.
    move=> H Hdistinct; specialize H with defs' uses'; move: H.
    impl_tac; trivial.
    impl_tac; trivial.
    move=> [HEq1 [HEq2 [type_soundness1 [all_acc_valid' [all_valid_acc [imp_partial_valid1 [type_soundness2 imp_partial_valid2]]]]]]] full_eq.
    case_eq (clean_def_tree defs').
    2: by move=> HEq; rewrite HEq in full_eq.
    move=> defs'' clean_eq; rewrite clean_eq in full_eq.
    apply (clean_def_tree_soundness eqns _ (map snd tctxt)) in clean_eq; trivial.
    {
        inversion full_eq as [[H1 H2]]; destruct H1; destruct H2.
        destruct clean_eq as [FstEq [same_trees [undef [valid type_soundness']]]].
        rewrite <-FstEq.
        do 5 (split; [> assumption | idtac ]).
        split.
        {
            rewrite Forall_forall; rewrite Forall_forall in all_acc_valid'.
            move=> [vars expr] LIn; apply all_acc_valid' in LIn; clear all_acc_valid'.
            destruct LIn as [in_vars in_expr]; split; [> idtac | assumption ].
            rewrite Forall_forall; rewrite Forall_forall in in_vars.
            move=> var LIn; apply in_vars in LIn; clear in_vars.
            move: same_trees FstEq LIn; clear.
            unfold valid_var_dtree, valid_var_dtree'.
            destruct var as [v|[v|]].
            3: by trivial.
            all: move: defs''; induction defs' as [|[vdef def_hd] def_tl HRec].
            all: move=> [|[vdef' def_hd'] def_tl']; simpl.
            all: move=> lr; inversion lr; trivial.
            by move=> _ Abs _; apply Abs; reflexivity.
            all: move=> HEq; inversion HEq; destruct ident_beq.
            by discriminate.
            1,3: by apply HRec; assumption.
            destruct def_hd'; trivial.
            apply keep_valid_acces_change_dtree; assumption.
        }
        clear FstEq.
        split; rewrite Forall_forall.
        {
            move=> [x [t|]] LIn; [> apply valid | apply undef]; trivial.
        }
        { 
            move=> [v t] LIn.
            rewrite Forall_forall in imp_partial_valid2.
            apply imp_partial_valid2 in LIn.
            apply partial_valid_use_tree_0; trivial.
        }
    }
    {
        rewrite Forall_forall in imp_partial_valid1.
        move=> v t LIn; refine (imp_partial_valid1 _ LIn).
    }
Qed.


(* TODO : continue sorting *)

Lemma test_if_inf_soundness:
    forall eqns trees vars,
        list_rel (r_dutree eqns) vars trees ->
        forall deps,
            update_all trees (length eqns) = deps ->
                forall i1 i2,
                i1 < length eqns ->
                test_if_inf deps i1 i2 = true <->
                exists v dpath upath,
                    List.In v vars /\
                    list_rel_top eq dpath upath /\
                    defined_in v dpath i1 eqns /\
                    used_in v upath i2 eqns.
Proof.
    unfold update_all.
    move=> eqns trees vars lr.
    induction lr as [|vhd [dtree utree] vtl ttl rel_hd rel_tl HRec]; simpl.
    all: move=> deps <- i1 i2 SInf.
    {
        split.
        {
            move=> Abs; exfalso.
            unfold test_if_inf in Abs.
            destruct (nth_error_genlist (@nil nat) (length eqns) i1) as [H| H].
            all: rewrite H in Abs; simpl in Abs.
            all: discriminate Abs.
        }
        {
            move=> [v [dpath [upath [[] _]]]].
        }
    }
    {
        destruct dtree as [dtree|].
        rewrite (test_if_inf_add_deps _ _ _ _ rel_hd); trivial.
        all: swap 1 2.
        {
            clear; induction ttl as [|[[hd1|] hd2] tl HRec]; simpl.
            by induction (length eqns); simpl; auto.
            by rewrite length_add_deps; assumption.
            by assumption.
        }
        all: rewrite (HRec _ Logic.eq_refl i1 i2); trivial; clear HRec SInf.
        all: split.
        {
            move=> [[v [dpath [upath [LIn [lrel [def used]]]]]]|[Abs|[dpath [upath [lrel [def used]]]]]].
            by exists v; exists dpath; exists upath; auto.
            by simpl in Abs; destruct Abs as [dpath [_ []]].
            unfold r_dutree in rel_hd.
            destruct rel_hd as [valid_def [valid_use _]].
            exists vhd; exists dpath; exists upath.
            split; [> left; reflexivity | idtac ].
            split; [> assumption | idtac ].
            rewrite (valid_is_defined_in _ _ _ _ _ _ valid_def) in def; simpl in def.
            destruct def.
            rewrite (valid_is_used_in _ _ _ _ _ _ valid_use) in used; simpl in used.
            destruct used.
            split; assumption.
        }
        {
            move=> [v [dpath [upath [[<-|LIn] H]]]].
            {
                destruct H as [lrel [def used]].
                right; right.
                unfold r_dutree in rel_hd.
                destruct rel_hd as [valid_def [valid_use [_ Forall_valid]]].
                exists dpath; exists upath.
                split; [> assumption | idtac ].
                split.
                {
                    rewrite (valid_is_defined_in _ _ _ _ _ _ valid_def); simpl.
                    split; [> idtac | assumption ].
                    rewrite Forall_forall in Forall_valid.
                    unfold defined_in in def.
                    destruct def as [vL [e [ind [nth_eq [is_spec LInCases]]]]].
                    apply nth_error_In in nth_eq; apply Forall_valid in nth_eq.
                    clear Forall_valid; destruct nth_eq as [Forall_valid _].
                    destruct LInCases as [LIn|[_ empty]].
                    2: by rewrite empty in is_spec; inversion is_spec; destruct dtree; simpl; trivial.
                    rewrite Forall_forall in Forall_valid.
                    apply Forall_valid in LIn; clear Forall_valid.
                    simpl in LIn; rewrite ident_beq_refl in LIn.
                    exact ((is_spec_preserve_dtree_valid_access _ _ _ is_spec LIn)).
                }
                {
                    rewrite (valid_is_used_in _ _ _ _ _ _ valid_use); simpl.
                    split; [> idtac | assumption ].
                    rewrite Forall_forall in Forall_valid.
                    unfold used_in in used.
                    destruct used as [vL [e [ind [nth_eq [is_spec LInCases]]]]].
                    apply nth_error_In in nth_eq; apply Forall_valid in nth_eq.
                    clear Forall_valid; destruct nth_eq as [_ Forall_valid].
                    destruct LInCases as [LIn|[_ empty]].
                    2: by rewrite empty in is_spec; inversion is_spec; destruct utree; simpl; trivial.
                    apply Forall_valid in LIn; clear Forall_valid.
                    simpl in LIn; rewrite ident_beq_refl in LIn.
                    exact ((is_spec_preserve_utree_valid_access _ _ _ is_spec LIn)).
                }
            }
            {
                left; do 3 eexists.
                split; [> exact LIn | exact H].
            }
        }
        {
            move=> [v [dpath [upath [LIn [top_eq H]]]]].
            exists v; exists dpath; exists upath; auto.
        }
        {
            simpl in rel_hd.
            move=> [v [dpath [upath [[Eq|LIn] [top_eq [def_in use_in]]]]]].
            2: by exists v; exists dpath; exists upath; auto.
            destruct Eq.
            destruct rel_hd as [_ [Abs _]].
            destruct (Abs _ _ def_in).
        }
    }
Qed.

Theorem build_definitions_soundness':
    forall tctxt eqns defs uses,
        distinct (map fst tctxt) ->
        build_definitions tctxt eqns = Some (defs, uses) ->
        map fst tctxt = map fst defs /\
        list_rel (r_dutree eqns) (map fst defs) (zip (map snd defs) (map snd uses)) /\
        Forall (fun p : list var * expr => let (vars, expr) := p in
            Forall (valid_var tctxt) vars /\
            forall v, Ensembles.In _ (expr_freefullvars expr) v -> valid_var tctxt v) eqns.
Proof.
    move=> tctxt eqns defs uses is_map build_eq.
    destruct (build_definitions_soundness _ _ _ _ is_map build_eq) as [Eq1 [Eq2 [ts_def [ts_used [AllValid [AllValid' [AllDef AllUsed]]]]]]].
    split; [> by assumption | idtac ].
    split; [> idtac | by assumption ].
    rewrite Eq1 in Eq2.
    assert (
        Forall (fun p : ident * option (def_tree nat) => let (vdef, dtree) := p in
            match dtree with
            | Some dtree =>
                Forall (fun p : list var * expr =>
                    Forall (fun v => dtree_valid_access_if_var vdef v dtree) p.1) eqns
            | None => True end) defs) as valid_accesses_defs.
    {
        rewrite Forall_forall.
        move=> [vdef [dtree|]] LIn; trivial.
        rewrite Forall_forall; move=> [vars expr] LIn_eqns; simpl.
        rewrite Forall_forall in AllValid'; apply AllValid' in LIn_eqns.
        destruct LIn_eqns as [all_vars _].
        rewrite Forall_forall; rewrite Forall_forall in all_vars.
        rewrite Eq1 in is_map.
        pose (p := is_map_soundness _ _ _ LIn is_map).
        move=> x LIn_vars; apply all_vars in LIn_vars.
        unfold valid_var_dtree' in LIn_vars; unfold dtree_valid_access_if_var.
        destruct x as [v|[v|]]; trivial.
        case_eq (ident_beq vdef v); trivial.
        rewrite ident_beq_eq; move=> Eq; destruct Eq.
        rewrite p in LIn_vars; assumption.
    }
    assert (
        Forall (fun p : ident * use_tree => let (vuse, utree) := p in
            Forall (fun p : seq var * expr =>
                forall var : var,
                    In usuba_AST.var (expr_freefullvars p.2) var ->
                    utree_valid_access_if_var vuse var utree) eqns) uses) as valid_accesses_uses.
    {
        rewrite Forall_forall.
        move=> [vuse utree] LIn; trivial.
        rewrite Forall_forall; move=> [vars expr] LIn_eqns; simpl.
        rewrite Forall_forall in AllValid'; apply AllValid' in LIn_eqns.
        destruct LIn_eqns as [_ all_expr].
        rewrite Eq1 in is_map; rewrite Eq2 in is_map.
        pose (p := is_map_soundness _ _ _ LIn is_map).
        move=> x LIn_expr; apply all_expr in LIn_expr.
        unfold valid_var_utree in LIn_expr; unfold utree_valid_access_if_var.
        destruct x as [v|[v|]]; trivial.
        case_eq (ident_beq vuse v); trivial.
        rewrite ident_beq_eq; move=> Eq; destruct Eq.
        rewrite p in LIn_expr; assumption.
    }
    clear is_map AllValid build_eq Eq1.
    clear AllValid'.
    move: ts_def uses ts_used Eq2 AllUsed valid_accesses_defs valid_accesses_uses.
    pose (types := map snd tctxt); fold types; move: types.
    induction AllDef as [|[vdef def_hd] def_tl AllDef_hd AllDef_tl HRec]; simpl.
    all: move=> [|typ types] def_ts; inversion def_ts; clear def_ts.
    all: move=> [|[vuse uses_hd] uses_tl]; simpl.
    all: move=> use_ts; inversion use_ts; clear use_ts.
    by intros; constructor.
    move=> LEq; inversion LEq as [[Eq_hd LEq_tl]]; destruct Eq_hd; clear LEq.
    move=> all_uvalid; inversion all_uvalid; clear all_uvalid.
    move=> all_daccess; inversion all_daccess as [|hd tl daccess]; clear all_daccess.
    move=> all_uaccess; inversion all_uaccess as [|hd' tl' uaccess]; clear all_uaccess.
    constructor.
    2: by apply (HRec types); assumption.
    unfold r_dutree.
    destruct def_hd as [def|].
    {
        split; [> assumption | idtac ].
        split; [> assumption | idtac ].
        split.
        by exists typ; split; assumption.
        rewrite Forall_forall.
        rewrite Forall_forall in daccess; rewrite Forall_forall in uaccess.
        move=> [vars expr] LIn_eqns; split.
        by apply daccess in LIn_eqns; simpl in LIn_eqns; assumption.
        by pose (p := uaccess _ LIn_eqns); simpl in p; assumption.
    }
    {
        split; [> assumption | idtac ].
        split; [> assumption | idtac ].
        rewrite Forall_forall.
        rewrite Forall_forall in uaccess.
        move=> [vars expr] LIn_eqns.
        pose (p := uaccess _ LIn_eqns); simpl in p; assumption.
    }
Qed.

Lemma test_distinct_soundness {A}:
    forall l1 l2,
        @test_distinct A l1 l2 = true ->
            distinct (map fst l1) /\
            Forall (fun el => List.In el (map fst l1) -> False) l2.
Proof.
    move=> l1; induction l1 as [|[i hd'] t1 HRec]; simpl.
    {
        move=> l2 _; split.
        by constructor.
        by rewrite Forall_forall; trivial.
    }
    {
        clear hd'.
        move=> l2; case_eq (List.existsb (ident_beq i) l2); simpl.
        by discriminate.
        move=> not_exists test_eq; apply HRec in test_eq; clear HRec.
        destruct test_eq as [is_map all_not_in].
        inversion all_not_in as [|hd' tl' not_in_hd not_in_tl].
        split.
        {
            constructor; trivial.
            rewrite Forall_forall.
            move=> x LIn HEq; destruct HEq.
            exact (not_in_hd LIn).
        }
        {
            rewrite Forall_forall; rewrite Forall_forall in not_in_tl.
            move=> x LIn [HEq|LIn'].
            {
                destruct HEq.
                rewrite <-not_true_iff_false in not_exists; apply not_exists.
                rewrite List.existsb_exists.
                eexists; rewrite ident_beq_eq.
                split; [> exact LIn | reflexivity ].
            }
            {
                exact (not_in_tl _ LIn LIn').
            }
        }
    }
Qed.

Lemma build_topological_sort_soundness:
    forall tctxt eqns ord,
        build_topological_sort tctxt eqns = Some ord ->
        is_topological_sort eqns ord /\
        Forall (fun p : list var * expr => let (vars, expr) := p in
            Forall (valid_var tctxt) vars /\ 
            forall v, Ensembles.In _ (expr_freefullvars expr) v -> valid_var tctxt v) eqns.
Proof.
    unfold build_topological_sort.
    move=> tctxt eqns ord.
    move: (test_distinct_soundness tctxt nil).
    destruct test_distinct.
    2: discriminate.
    impl_tac; [> reflexivity | idtac ].
    move=> [is_map _].
    move: (build_definitions_soundness' tctxt eqns).
    destruct build_definitions as [[defs uses]|].
    2: by discriminate.
    move=> build_defs_soundness build_order_eq.
    specialize build_defs_soundness with defs uses.
    destruct build_defs_soundness as [fst_eq [lrel all_valid]]; trivial.
    split; [> idtac | assumption ].
    apply build_order_soundness in build_order_eq.
    unfold is_topological_sort.
    destruct build_order_eq as [length_eq el_eq].
    split; [> by auto | idtac ].
    move=> v dpath upath i1 i2 top_eq used defined.
    move: (test_if_inf_soundness _ _ _ lrel _ Logic.eq_refl i2 i1).
    assert (i1 < length eqns) as i1_inf.
    {
        unfold used_in in used.
        destruct used as [vL [e [ind [nth_eq _]]]].
        apply/ltP; rewrite <-nth_error_Some; rewrite nth_eq.
        move=> Abs; discriminate Abs.
    }
    assert (i2 < length eqns) as i2_inf.
    {
        unfold defined_in in defined.
        destruct defined as [vL [e [ind [nth_eq _]]]].
        apply/ltP; rewrite <-nth_error_Some; rewrite nth_eq.
        move=> Abs; discriminate Abs.
    }
    impl_tac; [> by assumption | idtac ].
    rewrite <-length_eq in i1_inf; rewrite <-length_eq in i2_inf.
    move/ltP in i1_inf; move/ltP in i2_inf.
    rewrite <-nth_error_Some in i1_inf; rewrite <-nth_error_Some in i2_inf.
    move: (el_eq i2 i1); clear el_eq; move=> el_eq.
    destruct (nth_error _ i1); [> clear i1_inf | by destruct (i1_inf Logic.eq_refl) ].
    destruct (nth_error _ i2); [> clear i2_inf | by destruct (i2_inf Logic.eq_refl) ].
    move=> [_ H].
    do 2 eexists; repeat split.
    apply el_eq; trivial.
    apply H; clear H.
    do 3 eexists; split.
    2: split; [> idtac | by split; [> exact defined | exact used ]].
    {
        rewrite <-fst_eq.
        unfold defined_in in defined.
        destruct defined as [vL [e [ind [nth_eq [_ LInCases]]]]].
        apply nth_error_In in nth_eq.
        rewrite Forall_forall in all_valid; apply all_valid in nth_eq.
        destruct nth_eq as [forall_vars _].
        rewrite Forall_forall in forall_vars.
        destruct LInCases as [LIn|[LIn _]]; apply forall_vars in LIn; simpl in LIn.
        all: case_eq (find_val tctxt v).
        2,4: move=> Eq; rewrite Eq in LIn; [> destruct LIn | destruct (LIn Logic.eq_refl) ].
        all: move=> t find_eq; rewrite find_eq in LIn.
        all: apply find_val_In in find_eq.
        all: apply (in_map fst _ _) in find_eq; simpl in find_eq; assumption.
    }
    {
        move: top_eq; clear.
        move=> H; induction H; constructor; auto.
    }
Qed.

Definition unwrap oi :=
    match oi with
    | Some i => i
    | None => 0
    end.

Lemma is_spec_b_soundness:
    forall path ind,
        is_spec_b path ind = true <-> is_specialization' path ind.
Proof.
    move=> path; induction path as [|path_hd path_tl HRec]; simpl.
    {
        move=>[|ind_hd ind_tl]; split.
        {
            move=> _.
            refine (AddPath nil nil nil (LRnil _)).
        }
        {
            reflexivity.
        }
        {
            move=> H; discriminate.
        }
        {
            move=> H; inversion H as [path_nat path_ind path_tl is_spec H0 H1].
            destruct path_nat; simpl in *.
            2: by discriminate.
            inversion is_spec.
        }
    }
    {
        move=> [|ind_hd ind_tl].
        {
            split; auto.
            move=> _.
            refine (AddPath nil nil _ (LRnil _)).
        }
        specialize HRec with ind_tl.
        destruct ind_hd as [ae|ae1 ae2|aeL].
        {
            rewrite andb_true_iff; rewrite HRec.
            clear HRec.
            unfold eval_to_nat.
            case_eq (eval_arith_expr nil ae).
            all: swap 1 2.
            {
                move=> HEq_None; split.
                by move=> [H _]; discriminate.
                move=> H; inversion H as [path_nat path_ind path_tl' is_spec HEq1 HEq2].
                symmetry in HEq2; destruct HEq2.
                destruct path_nat; simpl in *.
                {
                    inversion is_spec.
                }
                inversion HEq1 as [HEq1_hd].
                clear HEq1.
                destruct H0.
                destruct HEq1_hd.
                inversion is_spec as [|h1 h2 t1 t2 is_spec_hd is_spec_tl].
                inversion is_spec_hd as [ae' i' HEq_Some| |].
                rewrite HEq_None in HEq_Some; discriminate.
            }
            {
                move=> n eval_eq; rewrite Nat.eqb_eq.
                split.
                {
                    move=> [-> H2].
                    inversion H2 as [path_nat path_ind path_tl' l_rel].
                    clear H2 H H0 path_tl path_ind.
                    apply (AddPath (n :: path_nat) _ _).
                    constructor; trivial.
                    constructor; assumption.
                }
                {
                    move=> H; inversion H as [path_nat path_ind path_tl' l_rel].
                    inversion l_rel as [|h1 h2 t1 t2 is_spec l_rel_tl].
                    destruct H2; simpl in *.
                    clear l_rel H3 H4 h2 t2.
                    split.
                    {
                        inversion is_spec as [ae' i eval_eq'| |].
                        move: eval_eq'; rewrite eval_eq.
                        inversion H0.
                        clear.
                        move=> H; inversion H; auto.
                    }
                    {
                        inversion H0.
                        constructor; auto.
                    }
                }
            }
        }
        {
            case_eq (eval_arith_expr nil ae1).
            all: swap 1 2.
            {
                move=> HEq_None; split; [> by idtac | idtac ].
                move=> H; inversion H as [path_nat path_ind path_tl' l_rel].
                inversion l_rel as [|h1 h2 t1 t2 is_spec].
                inversion is_spec as [| |ae1' ae2' i1 i2 i HEq_Some].
                rewrite HEq_None in HEq_Some; discriminate.
            }
            move=> i1 eval_eq1.
            case_eq  (eval_arith_expr nil ae2).
            all: swap 1 2.
            {
                move=> HEq_None; split; [> by idtac | idtac ].
                move=> H; inversion H as [path_nat path_ind path_tl' l_rel].
                inversion l_rel as [|h1 h2 t1 t2 is_spec].
                inversion is_spec as [| |ae1' ae2' i1' i2 i _ HEq_Some].
                rewrite HEq_None in HEq_Some; discriminate.
            }
            move=> i2 eval_eq2.
            rewrite andb_true_iff.
            rewrite orb_true_iff.
            do 2 rewrite andb_true_iff.
            rewrite HRec; clear HRec.
            split.
            {
                move=> [HIn_raw H2].
                inversion H2 as [path_nat path_ind path_tl' l_rel].
                clear H2 H H0 path_tl path_ind.
                apply (AddPath (path_hd :: path_nat) _ _).
                constructor; trivial.
                apply (SpecRange _ _ _ _ _ eval_eq1 eval_eq2).
                assumption.
            }
            {
                move=> H; inversion H as [path_nat path_ind path_tl' l_rel].
                inversion l_rel as [|h1 h2 t1 t2 is_spec l_rel_tl].
                destruct H2; simpl in *.
                clear l_rel H3 H4 h2 t2.
                split.
                {
                    inversion is_spec as [| |ae1' ae2' i1' i2' i eval_eq1' eval_eq2' HIn].
                    rewrite eval_eq1 in eval_eq1'; clear eval_eq1.
                    rewrite eval_eq2 in eval_eq2'; clear eval_eq2.
                    inversion eval_eq1' as [H']; destruct H'; clear eval_eq1'.
                    inversion eval_eq2' as [H']; destruct H'; clear eval_eq2'.
                    inversion H0 as [H']; destruct H'.
                    assumption.
                }
                {
                    inversion H0.
                    constructor; auto.
                }
            }
        }
        {
            rewrite andb_true_iff; rewrite HRec; clear HRec.
            split.
            {
                move=> [Hexists Hspec].
                rewrite existsb_exists in Hexists.
                destruct Hexists as [ae [HIn eval_to_is_true]].
                inversion Hspec as [path_nat path_ind path_tl' l_rel].
                clear Hspec H path_tl H0 path_ind.
                apply (AddPath (_ :: _) _ _).
                constructor; auto.
                apply (SpecSlice ae); auto.
                unfold eval_to_nat in eval_to_is_true.
                destruct eval_arith_expr.
                by rewrite Nat.eqb_eq in eval_to_is_true; destruct eval_to_is_true.
                by discriminate.
            }
            {
                move=> H; inversion H as [path_nat path_ind path_tl' l_rel].
                clear H H1 path_ind.
                inversion l_rel as [|h1 h2 t1 t2 is_spec l_rel_tl].
                destruct H; clear H1 h2 H2 t2.
                simpl in *.
                inversion is_spec as [|ae aeL' i HIn eval_eq|].
                clear H i H1 aeL'.
                split.
                {
                    rewrite existsb_exists; eexists.
                    split; [> exact HIn | idtac].
                    unfold eval_to_nat; rewrite eval_eq.
                    inversion H0; rewrite Nat.eqb_eq; reflexivity.
                }
                {
                    inversion H0; constructor; trivial.
                }
            }
        }
    }
Qed.

Fixpoint get_len_of_array {A} (l : list A) (t : typ) : option nat :=
    match t with
    | Array t len =>
        match l with
        | nil => Some len
        | _ :: l => get_len_of_array l t
        end
    | _ => None
    end.

Fixpoint get_typ_of_array {A} (l : list A) (t : typ) : option typ :=
    match l with
    | nil => Some t
    | _ :: l => match t with
        | Array t _ => get_typ_of_array l t
        | _ => None
        end
    end.
    
Definition gen_range' (olen : option (option nat)) : list nat :=
    match olen with
    | None | Some None => nil
    | Some (Some len) => gen_range 0 (len - 1)
    end.

Inductive acc_pred : list (ident * typ) -> list (list var * expr) -> expr -> Prop :=
    | AccConst : forall tctxt eqns z otyp, acc_pred tctxt eqns (Const z otyp)
    | AccExpVar : forall tctxt eqns v, acc_var v nil nil tctxt eqns -> acc_pred tctxt eqns (ExpVar (Var v))
    | AccExpVarInd : forall tctxt eqns v ind, acc_var v nil ind tctxt eqns -> acc_pred tctxt eqns (ExpVar (Index (Var v) ind))
    | AccTuple : forall tctxt eqns el, acc_pred_l tctxt eqns el -> acc_pred tctxt eqns (Tuple el)
    | AccBuildArray : forall tctxt eqns el, acc_pred_l tctxt eqns el -> acc_pred tctxt eqns (BuildArray el)
    | AccNot : forall tctxt eqns e, acc_pred tctxt eqns e -> acc_pred tctxt eqns (Not e)
    | AccAop : forall tctxt eqns aop e1 e2, acc_pred tctxt eqns e1 -> acc_pred tctxt eqns e2 -> acc_pred tctxt eqns (Arith aop e1 e2)
    | AccLop : forall tctxt eqns lop e1 e2, acc_pred tctxt eqns e1 -> acc_pred tctxt eqns e2 -> acc_pred tctxt eqns (Log lop e1 e2)
    | AccShift : forall tctxt eqns sop e ae, acc_pred tctxt eqns e -> acc_pred tctxt eqns (Shift sop e ae)
    | AccShuffle : forall tctxt eqns v l, acc_var v nil nil tctxt eqns -> acc_pred tctxt eqns (Shuffle (Var v) l)
    | AccShuffleInd : forall tctxt eqns v l ind, acc_var v nil ind tctxt eqns -> acc_pred tctxt eqns (Shuffle (Index (Var v) ind) l)
    | AccBitmask : forall tctxt eqns e ae, acc_pred tctxt eqns e -> acc_pred tctxt eqns (Bitmask e ae)
    | AccPack : forall tctxt eqns e1 e2 otyp, acc_pred tctxt eqns e1 -> acc_pred tctxt eqns e2 -> acc_pred tctxt eqns (Pack e1 e2 otyp)
    | AccFun : forall tctxt eqns v el, acc_pred_l tctxt eqns el -> acc_pred tctxt eqns (Fun v el)
    | AccFun_v : forall tctxt eqns v ae el, acc_pred_l tctxt eqns el -> acc_pred tctxt eqns (Fun_v v ae el)
with acc_pred_l : list (ident * typ) -> list (list var * expr) -> expr_list -> Prop :=
    | AccEnil : forall tctxt eqns, acc_pred_l tctxt eqns Enil
    | AccECons : forall tctxt eqns e el, acc_pred tctxt eqns e -> acc_pred_l tctxt eqns el -> acc_pred_l tctxt eqns (ECons e el)
with acc_find_var : ident -> list nat -> list (list var * expr) -> list (ident * typ) -> list (list var * expr) -> Prop :=
    | AccFindIn : forall v path_nat eqns tctxt eqns' vL e,
        acc_pred tctxt eqns e ->
        generalization_in v path_nat vL = true ->
        acc_find_var v path_nat ((vL, e) :: eqns') tctxt eqns
    | AccFindNil : forall v path_nat tctxt eqns,
        acc_find_var v path_nat nil tctxt eqns
    | AccNotFind : forall v path_nat tctxt eqns eqns' vL e,
        acc_find_var v path_nat eqns' tctxt eqns ->
        generalization_in v path_nat vL = false ->
        acc_find_var v path_nat ((vL, e) :: eqns') tctxt eqns
with acc_var : ident -> list nat -> list indexing -> list (ident * typ) -> list (list var * expr) -> Prop :=
    | AccVarFinished : forall v path_nat tctxt eqns,
        acc_find_var v path_nat eqns tctxt eqns ->
        acc_forall v path_nat nil tctxt eqns [seq Const_e (Z.of_nat i) | i <- gen_range' (omap (get_len_of_array path_nat) (find_val tctxt v))] ->
        acc_var v path_nat nil tctxt eqns
    | AccVarInd : forall v path_nat path_tl ae tctxt eqns,
        acc_find_var v path_nat eqns tctxt eqns ->
        acc_var v (path_nat ++ [:: unwrap (eval_arith_expr nil ae)]) path_tl tctxt eqns ->
        acc_var v path_nat (IInd ae::path_tl) tctxt eqns
    | AccVarRange : forall v path_nat path_tl ae1 ae2 tctxt eqns,
        acc_find_var v path_nat eqns tctxt eqns ->
        acc_forall v path_nat path_tl tctxt eqns [seq Const_e (Z.of_nat i) | i <- gen_range (unwrap (eval_arith_expr nil ae1)) (unwrap (eval_arith_expr nil ae2))] ->
        acc_var v path_nat (IRange ae1 ae2::path_tl) tctxt eqns
    | AccVarSlice : forall v path_nat path_tl aeL tctxt eqns,
        acc_find_var v path_nat eqns tctxt eqns ->
        acc_forall v path_nat path_tl tctxt eqns aeL ->
        acc_var v path_nat (ISlice aeL::path_tl) tctxt eqns
with acc_forall : ident -> list nat -> list indexing -> list (ident * typ) -> list (list var * expr) -> list arith_expr -> Prop :=
    | AccForallNil : forall v path_nat path_tl tctxt eqns,
        acc_forall v path_nat path_tl tctxt eqns nil
    | AccForallCons : forall v path_nat path_tl tctxt eqns ae_hd ae_tl,
        acc_var v (path_nat ++ [:: unwrap (eval_arith_expr nil ae_hd)]) path_tl tctxt eqns ->
        acc_forall v path_nat path_tl tctxt eqns ae_tl ->
        acc_forall v path_nat path_tl tctxt eqns (ae_hd :: ae_tl)
.

Lemma get_typ_of_array_concat {A : Type}:
    forall (path_in path_tl : list A) t,
        get_typ_of_array (path_in ++ path_tl) t
            = 
            match get_typ_of_array path_in t with
            | Some t' => get_typ_of_array path_tl t'
            | None => None
            end.
Proof.
    move=> path_in path_tl; induction path_in; simpl; trivial.
    move=> []; trivial.
Qed.


Lemma get_len_of_array_to_typ {A : Type}:
    forall (path : list A) t,
        get_len_of_array path t = 
            match get_typ_of_array path t with
            | Some t' => @get_len_of_array A nil t'
            | None => None
            end.
Proof.
    move=> path; induction path; simpl; trivial.
    move=> []; trivial.
Qed.

Lemma get_len_of_array_None:
    forall v tctxt eqns path_in,
        (forall i, omap (get_len_of_array path_in) (find_val tctxt v) <> Some (Some i)) ->
        (forall (pos : nat) (path : seq nat), list_rel_top eq path_in path -> defined_in v path pos eqns -> False) ->
        acc_var v path_in [::] tctxt eqns.
Proof.
    move=> v tctxt eqns path_in is_err defined.
    refine (AccVarFinished _ _ _ _ _ _).
    {
        assert (forall eqns', acc_find_var v path_in eqns tctxt eqns') as H'.
        2: by auto.
        move=> eqns'.
        move: defined.
        induction eqns as [|[vars e] eqns_tl HRec].
        by constructor.
        move=> defined.
        apply AccNotFind.
        {
            apply HRec; move=> pos path def'.
            specialize defined with pos.+1 path; simpl in defined.
            auto.
        }
        {
            clear HRec.
            assert (forall path,
                (exists ind, list_rel is_specialization path ind /\
                        list_rel_top eq path_in path /\
                        (List.In (Index (Var v) ind) vars \/
                        List.In (Var v) vars /\ ind = [::])) -> False) as defined'.
            {
                move=> path [ind [is_spec [eq_top LIn]]].
                move: (defined 0 path); impl_tac; auto.
                impl_tac; auto.
                unfold defined_in; simpl.
                do 3 eexists; repeat split.
                by exact is_spec.
                by exact LIn.
            }
            clear defined.
            induction vars as [|vhd vtl HRec]; simpl; trivial.
            case_eq (is_generalization v path_in vhd).
            {
                move=> is_gen; exfalso; clear HRec is_err.
                destruct vhd as [v'|[v'|] ind]; simpl in *.
                3: by discriminate is_gen.
                {
                    rewrite ident_beq_eq in is_gen; destruct is_gen.
                    apply (defined' nil); eexists; split.
                    by constructor.
                    split.
                    by constructor.
                    by auto.
                }
                {
                    move/andP in is_gen; unfold is_true in is_gen.
                    rewrite ident_beq_eq in is_gen.
                    destruct is_gen as [-> is_spec].
                    rewrite is_spec_b_soundness in is_spec.
                    move: defined'.
                    inversion is_spec as [path_nat path_ind path_tl is_spec'].
                    move=> H'; specialize H' with path_nat; apply H'; clear H'.
                    exists ind.
                    split; [> assumption | split; auto ].
                    clear.
                    induction path_nat; simpl; constructor; trivial.
                }
            }
            {
                move=> _; apply HRec.
                move=> path [ind [is_spec [top_eq HIn]]]; apply (defined' path).
                exists ind; split; trivial.
                split; trivial.
                destruct HIn as [H|[H H']]; [> left | right; split; trivial ].
                all: by constructor.
            }
        }
    }
    {
        destruct find_val; simpl; [> simpl in is_err | by constructor ].
        destruct get_len_of_array as [i|]; simpl; [> exfalso; refine (is_err _ Logic.eq_refl) | by constructor ].
    }
Qed.

Lemma generalization_in_soudness:
    forall v path_in vars,
        generalization_in v path_in vars = true <->
            exists ind,
                is_specialization' path_in ind /\
                (List.In (Index (Var v) ind) vars \/
                List.In (Var v) vars /\ ind = nil).
Proof.
    move=> v path_in vars; induction vars as [|v_hd v_tl HRec]; simpl.
    {
        by split; [> idtac | move=> [ind [_ [[]|[[] _]]]]].
    }
    {
        unfold is_generalization.
        destruct v_hd as [v'|[v'|v' ind'] ind].
        {
            case_eq (ident_beq v v').
            {
                rewrite ident_beq_eq.
                move=> ->; split; trivial; move=> _.
                exists nil; split; auto.
                by refine (AddPath nil _ _ _); constructor.
            }
            {
                move=> Neg; rewrite HRec; clear HRec.
                split; move=> [ind [is_spec LIn]]; exists ind; split; trivial.
                by destruct LIn as [LIn|[LIn Eq]]; auto.
                destruct LIn as [[Abs|LIn]|[[VarEq|LIn] empty]]; auto.
                by inversion Abs.
                rewrite <-not_true_iff_false in Neg.
                exfalso; apply Neg; clear Neg.
                inversion VarEq.
                rewrite ident_beq_eq; reflexivity.
            }
        }
        {
            case_eq (ident_beq v v' && is_spec_b path_in ind).
            all:move/andP.
            {
                unfold is_true; rewrite ident_beq_eq.
                move=> [HEq_v is_spec]; split; trivial; move=> _.
                rewrite is_spec_b_soundness in is_spec.
                destruct HEq_v; exists ind; split; auto.
            }
            {
                move=> Neg; rewrite HRec; clear HRec.
                split; move=> [ind' [is_spec LIn]]; exists ind'; split; trivial.
                by destruct LIn as [LIn|[LIn Eq]]; auto.
                destruct LIn as [[Abs|LIn]|[[VarEq|LIn] empty]]; auto.
                2: by inversion VarEq.
                exfalso; apply Neg.
                inversion Abs; split.
                by unfold is_true; rewrite ident_beq_eq.
                unfold is_true; rewrite is_spec_b_soundness; auto.
            }
        }
        {
            rewrite HRec; clear HRec.
            split; move=> [new_ind [is_spec LIn]]; exists new_ind; split; trivial.
            by destruct LIn as [LIn|[LIn Eq]]; auto.
            destruct LIn as [[Abs|LIn]|[[Abs|LIn] empty]]; auto.
            all: by inversion Abs.
        }
    }
Qed.

Definition eval_to_some (ae : arith_expr) := match eval_arith_expr nil ae with None => false | Some _ => true end.

Definition valid_index (i : indexing) : Prop :=
    match i with
    | IInd ae => eval_to_some ae
    | ISlice aeL => Forall eval_to_some aeL /\ aeL <> nil
    | IRange ae1 ae2 => eval_to_some ae1 && eval_to_some ae2
    end.

Lemma valid_index_imp_exists:
    forall indL,
        Forall valid_index indL ->
        exists p_nat,
            list_rel is_specialization p_nat indL.
Proof.
    move=> indL validL; induction validL as [|ind tl valid_ind valid_tl [p_nat lrel]].
    by eexists; constructor.
    destruct ind as [ae|ae1 ae2|aeL]; simpl in valid_ind.
    {
        unfold eval_to_some in valid_ind.
        case_eq (eval_arith_expr nil ae).
        2: by move=> eval_None; rewrite eval_None in valid_ind; discriminate.
        move=> n eval_Some.
        eexists; constructor 2.
        2: exact lrel.
        constructor; exact eval_Some.
    }
    {
        move: valid_ind; move/andP.
        unfold eval_to_some; move=> [valid_ae1 valid_ae2].
        case_eq (eval_arith_expr nil ae1).
        2: by move=> eval_None; rewrite eval_None in valid_ae1; discriminate.
        case_eq (eval_arith_expr nil ae2).
        2: by move=> eval_None; rewrite eval_None in valid_ae2; discriminate.
        move=> i2 eval2 i1 eval1.
        eexists; constructor 2.
        2: exact lrel.
        refine (SpecRange _ _ _ _ _ _ _ _).
        by exact eval1.
        by exact eval2.
        destruct (Nat.le_gt_cases i1 i2) as [H|H]; move: H; [> move/leP | move/ltP]; move=> H.
        by left; split; [> exact H | auto ].
        by right; split; auto.
    }
    {
        destruct valid_ind as [valid_ind not_empty].
        move: not_empty; inversion valid_ind as [|ae aeL' valid_ae valid_aeL H].
        by idtac.
        destruct H; move=> _.
        unfold eval_to_some in valid_ae.
        case_eq (eval_arith_expr nil ae).
        2: by move=> H; rewrite H in valid_ae; discriminate.
        move=> n eval_some.
        eexists; constructor 2.
        2: exact lrel.
        refine (SpecSlice _ _ _ _ _).
        by constructor.
        by exact eval_some.
    }
Qed.

Lemma size_length {A}:
    forall l : seq A,
        size l = length l.
Proof.
    move=> l; induction l; simpl; auto.
Qed.

Lemma termination_proof_ind_lemma:
    forall v k path_in eqns_tl ord_tl tctxt,
        length eqns_tl = length ord_tl ->
    forall eqns_hd ord_hd,
        length eqns_hd = length ord_hd ->
        (forall pos path,
            list_rel_top eq path_in path ->
            length path <= length path_in ->
            defined_in v path pos (eqns_hd ++ eqns_tl) ->
            nth k.+1 (ord_hd ++ ord_tl) pos < k.+1) ->
        (forall v path_tl path_in,
            Forall valid_index path_tl ->
            (exists t : typ, find_val tctxt v = Some t /\
                match get_typ_of_array path_in t with
                | Some t' => valid_access t' path_tl
                | None => False end) ->
            (forall pos path1 path2,
                list_rel is_specialization path1 path_tl ->
                list_rel_top eq (path_in ++ path1) path2 ->
                defined_in v path2 pos (eqns_hd ++ eqns_tl) ->
                nth k (ord_hd ++ ord_tl) pos < k) ->
            acc_var v path_in path_tl tctxt (eqns_hd ++ eqns_tl)) ->
        is_topological_sort (eqns_hd ++ eqns_tl) (ord_hd ++ ord_tl) ->
        Forall (fun p : seq var * expr => let (vars, expr) := p in
            Forall (valid_var tctxt) vars /\
            (forall v : var, In var (expr_freefullvars expr) v -> valid_var tctxt v)) (eqns_hd ++ eqns_tl) ->
        acc_find_var v path_in eqns_tl tctxt (eqns_hd ++ eqns_tl).
Proof.
    move=> v k path_in eqns_tl; induction eqns_tl as [|[vars expr] eqns_tl HRec].
    by intros; constructor.
    move=> [|ord_el ord_tl]; simpl.
    all: move=> tctxt H; inversion H as [length_eq]; clear H.
    move=> eqns_hd ord_hd length_hd_eq defined HRec_k is_top type_soundness.
    case_eq (generalization_in v path_in vars).
    {
        move=> gen_in_true; pose (H := gen_in_true); move: H.
        apply AccFindIn.
        rewrite generalization_in_soudness in gen_in_true.
        destruct gen_in_true as [ind [is_spec' LIn]].
        inversion is_spec' as [path_nat path_ind path_tl is_spec H]; destruct H.
        specialize defined with (length ord_hd) path_nat; move: defined.
        impl_tac.
        by clear; induction path_nat; simpl; constructor; auto.
        impl_tac.
        {
            rewrite app_length; clear.
            induction (length path_nat); simpl; auto.
        }
        impl_tac.
        {
            unfold defined_in; rewrite <-length_hd_eq.
            rewrite nth_error_app2; trivial.
            rewrite Nat.sub_diag; simpl.
            do 3 eexists; repeat split.
            by exact is_spec.
            by exact LIn.
        }
        rewrite nth_cat; rewrite size_length.
        rewrite ltnn; rewrite subnn; simpl.
        clear HRec; move=> HInf.
        assert (forall v, In _ (expr_freefullvars expr) v -> valid_var tctxt v) as valid_vars.
        {
            rewrite Forall_app in type_soundness; destruct type_soundness as [_ type_soundness].
            inversion type_soundness as [|x l H_hd H_tl]; destruct H_hd; trivial.
        }
        clear type_soundness is_spec H0 path_ind LIn.
        assert (forall expr', is_subexpr expr' expr -> (forall v, In _ (expr_freefullvars expr') v -> valid_var tctxt v) -> acc_pred tctxt (eqns_hd ++ (vars, expr) :: eqns_tl) expr') as H.
        2: apply (H _ (is_subexpr_refl _)); trivial.
        clear valid_vars.
        refine (expr_find _ (fun exprl =>
            Forall (fun e => is_subexpr e expr) (list_of_expr_list exprl) ->
            (forall v, In var (exprl_freevars exprl) v -> valid_var tctxt v) ->
            acc_pred_l tctxt (eqns_hd ++ (vars, expr) :: eqns_tl) exprl) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
        (* Const *)
        {
            intros; constructor.
        }
        (* Var *)
        {
            intros v' is_sub H.
            specialize H with v'; move: H.
            impl_tac; [> by simpl; constructor | idtac ].
            move=> valid.
            destruct v' as [v'|[v'|] ind']; simpl in *.
            3: by destruct valid.
            all: constructor; apply HRec_k.
            {
                constructor.
            }
            {
                destruct find_val as [t|].
                2: by exfalso; apply valid; reflexivity.
                eexists; split; [> by reflexivity | idtac ].
                simpl; destruct t; simpl; trivial.
            }
            {
                move=> pos path1 path2 is_spec top_eq def_in.
                unfold is_topological_sort in is_top; destruct is_top as [_ is_top].
                specialize is_top with v' path2 nil (length eqns_hd) pos; move: is_top.
                impl_tac; [> by constructor | idtac ].
                impl_tac.
                {
                    unfold used_in.
                    rewrite nth_error_app2; trivial.
                    rewrite Nat.sub_diag; simpl.
                    do 3 eexists; repeat split.
                    by constructor.
                    right; split; trivial.
                    apply (is_subexpr_freefullvars _ _ is_sub).
                    simpl; constructor.
                }
                impl_tac; trivial.
                move=> [p_used' [p_def' [nth_used [nth_def HInf']]]].
                rewrite length_hd_eq in nth_used; rewrite nth_error_app2 in nth_used; trivial.
                rewrite Nat.sub_diag in nth_used; simpl in nth_used.
                assert (nth k (ord_hd ++ ord_el :: ord_tl) pos = p_def') as ->.
                {
                    move: nth_def; clear.
                    pose (l := ord_hd ++ ord_el :: ord_tl); fold l; move: l pos; clear.
                    move=> l; induction l; move=> [|pos]; simpl.
                    1-3: move=> H; inversion H; trivial.
                    auto.
                }
                inversion nth_used as [H]; destruct H; clear nth_used.
                apply/ltP; move/ltP in HInf'.
                apply (Nat.lt_le_trans _ _ _ HInf').
                apply le_S_n; apply/leP; assumption.
            }
            {
                destruct find_val; [> idtac | destruct valid ].
                move: valid; clear.
                move: t; induction ind' as [|ind tl HRec].
                by intros; constructor.
                move=> [|d m|t len]; simpl.
                1,2: by move=> H; inversion H.
                move=> [valid_tl valid_ind]; constructor; [> idtac | exact (HRec t valid_tl) ].
                destruct ind as [ae|ae1 ae2|aeL]; simpl.
                all: unfold eval_lt in valid_ind; unfold eval_to_some.
                by destruct eval_arith_expr.
                by destruct valid_ind; destruct eval_arith_expr; destruct eval_arith_expr.
                destruct valid_ind as [valid_ind not_empty].
                split; trivial.
                move: valid_ind; clear.
                move=> H; induction H; constructor; trivial; destruct eval_arith_expr; auto.
            }
            {
                destruct find_val as [t|]; [> idtac | by destruct valid ].
                eexists; split; trivial.
            }
            {
                move=> pos path1 path2 is_spec top_eq def_in.
                unfold is_topological_sort in is_top; destruct is_top as [_ is_top].
                specialize is_top with v' path2 path1 (length eqns_hd) pos; move: is_top.
                impl_tac; [> by assumption | idtac ].
                impl_tac.
                {
                    unfold used_in.
                    rewrite nth_error_app2; trivial.
                    rewrite Nat.sub_diag; simpl.
                    do 3 eexists; repeat split.
                    by exact is_spec.
                    left; apply (is_subexpr_freefullvars _ _ is_sub).
                    simpl; constructor.
                }
                impl_tac; trivial.
                move=> [p_used' [p_def' [nth_used [nth_def HInf']]]].
                rewrite length_hd_eq in nth_used; rewrite nth_error_app2 in nth_used; trivial.
                rewrite Nat.sub_diag in nth_used; simpl in nth_used.
                assert (nth k (ord_hd ++ ord_el :: ord_tl) pos = p_def') as ->.
                {
                    move: nth_def; clear.
                    pose (l := ord_hd ++ ord_el :: ord_tl); fold l; move: l pos; clear.
                    move=> l; induction l; move=> [|pos]; simpl.
                    1-3: move=> H; inversion H; trivial.
                    auto.
                }
                inversion nth_used as [H]; destruct H; clear nth_used.
                apply/ltP; move/ltP in HInf'.
                apply (Nat.lt_le_trans _ _ _ HInf').
                apply le_S_n; apply/leP; assumption.
            }
        }
        (* Tuple *)
        {
            simpl.
            intros eL HRec is_sub valid.
            constructor; apply HRec; trivial.
            move: is_sub; clear.
            assert (forall eL_hd, (Forall (fun e => (exists e', List.In e' eL_hd /\ is_subexpr e e') \/ is_subexpr_l e eL)) (eL_hd ++ list_of_expr_list eL)).
            {
                induction eL as [|hd tl HRec]; simpl.
                {
                    move=> eL_hd; rewrite cats0.
                    rewrite Forall_forall.
                    move=> e HIn; left.
                    exists e; split; trivial.
                    apply is_subexpr_refl.
                }
                {
                    move=> eL_hd.
                    specialize HRec with (eL_hd ++ [:: hd]).
                    rewrite <-app_assoc in HRec; simpl in HRec.
                    rewrite Forall_forall in HRec; rewrite Forall_forall.
                    move=> e; specialize HRec with e.
                    rewrite List.in_app_iff; rewrite List.in_app_iff in HRec.
                    move=> [H|H].
                    {
                        destruct HRec as [H1|]; auto.
                        destruct H1 as [e' [LIn is_sub]].
                        rewrite List.in_app_iff in LIn.
                        destruct LIn as [H'|H'].
                        {
                            left; exists e'; auto.
                        }
                        {
                            inversion H' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                            auto.
                        }
                    }
                    {
                        inversion H as [HEq|HIn].
                        {
                            destruct HEq; right; left; apply is_subexpr_refl.
                        }
                        {
                            destruct HRec as [[e' [HIn' is_sub]]|]; auto.
                            rewrite List.in_app_iff in HIn'.
                            destruct HIn' as [HIn'|HIn'].
                            {
                                left; exists e'; auto.
                            }
                            {
                                inversion HIn' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                                auto.
                            }
                        }
                    }
                }
            }
            specialize H with nil.
            rewrite Forall_forall; rewrite Forall_forall in H.
            move=> is_sub e HIn; specialize H with e.
            simpl in H; apply H in HIn; clear H.
            destruct HIn as [[e' [[] H]]|is_sub'].
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; assumption.
        }
        (* BuildArray *)
        {
            simpl.
            intros eL HRec is_sub valid.
            constructor; apply HRec; trivial.
            move: is_sub; clear.
            assert (forall eL_hd, (Forall (fun e => (exists e', List.In e' eL_hd /\ is_subexpr e e') \/ is_subexpr_l e eL)) (eL_hd ++ list_of_expr_list eL)).
            {
                induction eL as [|hd tl HRec]; simpl.
                {
                    move=> eL_hd; rewrite cats0.
                    rewrite Forall_forall.
                    move=> e HIn; left.
                    exists e; split; trivial.
                    apply is_subexpr_refl.
                }
                {
                    move=> eL_hd.
                    specialize HRec with (eL_hd ++ [:: hd]).
                    rewrite <-app_assoc in HRec; simpl in HRec.
                    rewrite Forall_forall in HRec; rewrite Forall_forall.
                    move=> e; specialize HRec with e.
                    rewrite List.in_app_iff; rewrite List.in_app_iff in HRec.
                    move=> [H|H].
                    {
                        destruct HRec as [H1|]; auto.
                        destruct H1 as [e' [LIn is_sub]].
                        rewrite List.in_app_iff in LIn.
                        destruct LIn as [H'|H'].
                        {
                            left; exists e'; auto.
                        }
                        {
                            inversion H' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                            auto.
                        }
                    }
                    {
                        inversion H as [HEq|HIn].
                        {
                            destruct HEq; right; left; apply is_subexpr_refl.
                        }
                        {
                            destruct HRec as [[e' [HIn' is_sub]]|]; auto.
                            rewrite List.in_app_iff in HIn'.
                            destruct HIn' as [HIn'|HIn'].
                            {
                                left; exists e'; auto.
                            }
                            {
                                inversion HIn' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                                auto.
                            }
                        }
                    }
                }
            }
            specialize H with nil.
            rewrite Forall_forall; rewrite Forall_forall in H.
            move=> is_sub e HIn; specialize H with e.
            simpl in H; apply H in HIn; clear H.
            destruct HIn as [[e' [[] H]]|is_sub'].
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; assumption.
        }
        (* Not *)
        {
            move=> e HRec is_sub valid.
            intros; constructor.
            apply HRec; trivial.
            refine (is_subexpr_trans _ _ _ _ is_sub).
            simpl; right; apply is_subexpr_refl.
        }
        (* Log *)
        {
            move=> lop e1 HRec1 e2 HRec2 is_sub valid.
            intros; constructor; [> apply HRec1 | apply HRec2 ].
            1,3: refine (is_subexpr_trans _ _ _ _ is_sub); simpl.
            1,2: right; [> left | right ]; apply is_subexpr_refl.
            all: intros; apply valid; constructor; assumption.
        }
        (* Arith *)
        {
            move=> aop e1 HRec1 e2 HRec2 is_sub valid.
            intros; constructor; [> apply HRec1 | apply HRec2 ].
            1,3: refine (is_subexpr_trans _ _ _ _ is_sub); simpl.
            1,2: right; [> left | right ]; apply is_subexpr_refl.
            all: intros; apply valid; constructor; assumption.
        }
        (* Shift *)
        {
            move=> s e HRec a is_sub valid.
            intros; constructor.
            apply HRec; trivial.
            refine (is_subexpr_trans _ _ _ _ is_sub).
            simpl; right; apply is_subexpr_refl.
        }
        (* Shuffle *)
        {
            intros v' iL is_sub H.
            specialize H with v'; move: H.
            impl_tac; [> by simpl; constructor | idtac ].
            move=> valid.
            destruct v' as [v'|[v'|] ind']; simpl in *.
            3: by destruct valid.
            all: constructor; apply HRec_k.
            {
                constructor.
            }
            {
                destruct find_val as [t|].
                2: by exfalso; apply valid; reflexivity.
                eexists; split; [> by reflexivity | idtac ].
                simpl; destruct t; simpl; trivial.
            }
            {
                move=> pos path1 path2 is_spec top_eq def_in.
                unfold is_topological_sort in is_top; destruct is_top as [_ is_top].
                specialize is_top with v' path2 nil (length eqns_hd) pos; move: is_top.
                impl_tac; [> by constructor | idtac ].
                impl_tac.
                {
                    unfold used_in.
                    rewrite nth_error_app2; trivial.
                    rewrite Nat.sub_diag; simpl.
                    do 3 eexists; repeat split.
                    by constructor.
                    right; split; trivial.
                    apply (is_subexpr_freefullvars _ _ is_sub).
                    simpl; constructor.
                }
                impl_tac; trivial.
                move=> [p_used' [p_def' [nth_used [nth_def HInf']]]].
                rewrite length_hd_eq in nth_used; rewrite nth_error_app2 in nth_used; trivial.
                rewrite Nat.sub_diag in nth_used; simpl in nth_used.
                assert (nth k (ord_hd ++ ord_el :: ord_tl) pos = p_def') as ->.
                {
                    move: nth_def; clear.
                    pose (l := ord_hd ++ ord_el :: ord_tl); fold l; move: l pos; clear.
                    move=> l; induction l; move=> [|pos]; simpl.
                    1-3: move=> H; inversion H; trivial.
                    auto.
                }
                inversion nth_used as [H]; destruct H; clear nth_used.
                apply/ltP; move/ltP in HInf'.
                apply (Nat.lt_le_trans _ _ _ HInf').
                apply le_S_n; apply/leP; assumption.
            }
            {
                destruct find_val; [> idtac | destruct valid ].
                move: valid; clear.
                move: t; induction ind' as [|ind tl HRec].
                by intros; constructor.
                move=> [|d m|t len]; simpl.
                1,2: by move=> H; inversion H.
                move=> [valid_tl valid_ind]; constructor; [> idtac | exact (HRec t valid_tl) ].
                destruct ind as [ae|ae1 ae2|aeL]; simpl.
                all: unfold eval_lt in valid_ind; unfold eval_to_some.
                by destruct eval_arith_expr.
                by destruct valid_ind; destruct eval_arith_expr; destruct eval_arith_expr.
                destruct valid_ind as [valid_ind not_empty].
                split; trivial.
                move: valid_ind; clear.
                move=> H; induction H; constructor; trivial; destruct eval_arith_expr; auto.
            }
            {
                destruct find_val as [t|]; [> idtac | by destruct valid ].
                eexists; split; trivial.
            }
            {
                move=> pos path1 path2 is_spec top_eq def_in.
                unfold is_topological_sort in is_top; destruct is_top as [_ is_top].
                specialize is_top with v' path2 path1 (length eqns_hd) pos; move: is_top.
                impl_tac; [> by assumption | idtac ].
                impl_tac.
                {
                    unfold used_in.
                    rewrite nth_error_app2; trivial.
                    rewrite Nat.sub_diag; simpl.
                    do 3 eexists; repeat split.
                    by exact is_spec.
                    left; apply (is_subexpr_freefullvars _ _ is_sub).
                    simpl; constructor.
                }
                impl_tac; trivial.
                move=> [p_used' [p_def' [nth_used [nth_def HInf']]]].
                rewrite length_hd_eq in nth_used; rewrite nth_error_app2 in nth_used; trivial.
                rewrite Nat.sub_diag in nth_used; simpl in nth_used.
                assert (nth k (ord_hd ++ ord_el :: ord_tl) pos = p_def') as ->.
                {
                    move: nth_def; clear.
                    pose (l := ord_hd ++ ord_el :: ord_tl); fold l; move: l pos; clear.
                    move=> l; induction l; move=> [|pos]; simpl.
                    1-3: move=> H; inversion H; trivial.
                    auto.
                }
                inversion nth_used as [H]; destruct H; clear nth_used.
                apply/ltP; move/ltP in HInf'.
                apply (Nat.lt_le_trans _ _ _ HInf').
                apply le_S_n; apply/leP; assumption.
            }
        }
        (* Bismask *)
        {
            move=> e HRec a is_sub valid.
            intros; constructor.
            apply HRec; trivial.
            refine (is_subexpr_trans _ _ _ _ is_sub).
            simpl; right; apply is_subexpr_refl.
        }
        (* Pack *)
        {
            move=> e1 HRec1 e2 HRec2 top is_sub valid.
            intros; constructor; [> apply HRec1 | apply HRec2 ].
            1,3: refine (is_subexpr_trans _ _ _ _ is_sub); simpl.
            1,2: right; [> left | right ]; apply is_subexpr_refl.
            all: intros; apply valid; constructor; assumption.
        }
        (* Fun *)
        {
            simpl.
            intros i eL HRec is_sub valid.
            constructor; apply HRec; trivial.
            move: is_sub; clear.
            assert (forall eL_hd, (Forall (fun e => (exists e', List.In e' eL_hd /\ is_subexpr e e') \/ is_subexpr_l e eL)) (eL_hd ++ list_of_expr_list eL)).
            {
                induction eL as [|hd tl HRec]; simpl.
                {
                    move=> eL_hd; rewrite cats0.
                    rewrite Forall_forall.
                    move=> e HIn; left.
                    exists e; split; trivial.
                    apply is_subexpr_refl.
                }
                {
                    move=> eL_hd.
                    specialize HRec with (eL_hd ++ [:: hd]).
                    rewrite <-app_assoc in HRec; simpl in HRec.
                    rewrite Forall_forall in HRec; rewrite Forall_forall.
                    move=> e; specialize HRec with e.
                    rewrite List.in_app_iff; rewrite List.in_app_iff in HRec.
                    move=> [H|H].
                    {
                        destruct HRec as [H1|]; auto.
                        destruct H1 as [e' [LIn is_sub]].
                        rewrite List.in_app_iff in LIn.
                        destruct LIn as [H'|H'].
                        {
                            left; exists e'; auto.
                        }
                        {
                            inversion H' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                            auto.
                        }
                    }
                    {
                        inversion H as [HEq|HIn].
                        {
                            destruct HEq; right; left; apply is_subexpr_refl.
                        }
                        {
                            destruct HRec as [[e' [HIn' is_sub]]|]; auto.
                            rewrite List.in_app_iff in HIn'.
                            destruct HIn' as [HIn'|HIn'].
                            {
                                left; exists e'; auto.
                            }
                            {
                                inversion HIn' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                                auto.
                            }
                        }
                    }
                }
            }
            specialize H with nil.
            rewrite Forall_forall; rewrite Forall_forall in H.
            move=> is_sub e HIn; specialize H with e.
            simpl in H; apply H in HIn; clear H.
            destruct HIn as [[e' [[] H]]|is_sub'].
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; assumption.
        }
        (* Fun_v *)
        {
            simpl.
            intros i a eL HRec is_sub valid.
            constructor; apply HRec; trivial.
            move: is_sub; clear.
            assert (forall eL_hd, (Forall (fun e => (exists e', List.In e' eL_hd /\ is_subexpr e e') \/ is_subexpr_l e eL)) (eL_hd ++ list_of_expr_list eL)).
            {
                induction eL as [|hd tl HRec]; simpl.
                {
                    move=> eL_hd; rewrite cats0.
                    rewrite Forall_forall.
                    move=> e HIn; left.
                    exists e; split; trivial.
                    apply is_subexpr_refl.
                }
                {
                    move=> eL_hd.
                    specialize HRec with (eL_hd ++ [:: hd]).
                    rewrite <-app_assoc in HRec; simpl in HRec.
                    rewrite Forall_forall in HRec; rewrite Forall_forall.
                    move=> e; specialize HRec with e.
                    rewrite List.in_app_iff; rewrite List.in_app_iff in HRec.
                    move=> [H|H].
                    {
                        destruct HRec as [H1|]; auto.
                        destruct H1 as [e' [LIn is_sub]].
                        rewrite List.in_app_iff in LIn.
                        destruct LIn as [H'|H'].
                        {
                            left; exists e'; auto.
                        }
                        {
                            inversion H' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                            auto.
                        }
                    }
                    {
                        inversion H as [HEq|HIn].
                        {
                            destruct HEq; right; left; apply is_subexpr_refl.
                        }
                        {
                            destruct HRec as [[e' [HIn' is_sub]]|]; auto.
                            rewrite List.in_app_iff in HIn'.
                            destruct HIn' as [HIn'|HIn'].
                            {
                                left; exists e'; auto.
                            }
                            {
                                inversion HIn' as [HEq|Abs]; [> destruct HEq | inversion Abs].
                                auto.
                            }
                        }
                    }
                }
            }
            specialize H with nil.
            rewrite Forall_forall; rewrite Forall_forall in H.
            move=> is_sub e HIn; specialize H with e.
            simpl in H; apply H in HIn; clear H.
            destruct HIn as [[e' [[] H]]|is_sub'].
            refine (is_subexpr_trans _ _ _ _ is_sub); auto.
            simpl; right; assumption.
        }
        (* Enil *)
        {
            intros; constructor.
        }
        (* ECons *)
        {
            simpl.
            move=> hd HRec_hd tl HRec_tl all_sub All_valid.
            constructor; inversion all_sub.
            all: [> apply HRec_hd | apply HRec_tl ]; trivial.
            all: by intros; apply All_valid; constructor.
        }
    }
    {
        apply AccNotFind.
        move: (HRec ord_tl tctxt length_eq (eqns_hd ++ [:: (vars, expr)]) (ord_hd ++ [:: ord_el])); clear HRec.
        do 2 rewrite <-app_assoc; simpl.
        do 2 rewrite app_length; simpl; rewrite length_hd_eq.
        repeat (impl_tac; trivial).
    }
Qed.

Lemma termination_lemma:
    forall k tctxt eqns ord, is_topological_sort eqns ord ->
        Forall (fun p : list var * expr => let (vars, expr) := p in
            Forall (valid_var tctxt) vars /\ 
            forall v, Ensembles.In _ (expr_freefullvars expr) v -> valid_var tctxt v) eqns ->
        forall v path_tl path_in,
            Forall valid_index path_tl ->
            (exists t, find_val tctxt v = Some t /\
                match get_typ_of_array path_in t with
                | None => False
                | Some t' => valid_access t' path_tl (*get_typ_of_array path_tl t' <> None*)
                end) ->
            (forall pos path1 path2, 
                list_rel is_specialization path1 path_tl ->
                list_rel_top Logic.eq (path_in ++ path1) path2 ->
                defined_in v path2 pos eqns ->
                nth k ord pos < k) ->
            acc_var v path_in path_tl tctxt eqns.
Proof.
    move=> k tctxt eqns ord is_top eqns_type_sound; induction k as [|k HRec_k].
    {
        move=> v path_tl path_in forall_vindex; move: path_in.
        induction forall_vindex as [|ind path_tl valid_hd valid_tl HRec].
        {
            move=> path_in find_soundness defined.
            destruct find_soundness as [t [find_val_eq get_typ_soundness]].
            case_eq (get_typ_of_array path_in t).
            2: by move=> H; rewrite H in get_typ_soundness.
            move=> t'; clear get_typ_soundness.
            move: path_in defined.
            induction t' as [|d m|t' HRec len].
            all: move=> path_in defined get_typ_eq.
            all: move: (get_len_of_array_to_typ path_in t); rewrite get_typ_eq; simpl.
            1,2: move=> eq_None; apply (get_len_of_array_None _ _ _ _); auto.
            1,3: by move=> i; rewrite find_val_eq; simpl; rewrite eq_None; discriminate.
            1,2: move=> pos path ltop def; move: (defined pos nil path (LRnil _)); rewrite cats0.
            1,2: do 2 (impl_tac; trivial); auto.
            move=> eq_Some.
            refine (AccVarFinished _ _ _ _ _ _).
            {
                assert (forall eqns', acc_find_var v path_in eqns tctxt eqns') as H'.
                2: by auto.
                move=> eqns'.
                clear is_top HRec get_typ_eq eq_Some find_val_eq eqns_type_sound.
                move: ord defined.
                induction eqns as [|[vars e] eqns_tl HRec].
                by constructor.
                move=> ord defined.
                apply AccNotFind.
                {
                    apply (HRec nil); move=> pos path1 path2 is_spec lrel def.
                    move: (defined pos.+1 path1 path2 is_spec lrel def).
                    auto.
                }
                {
                    clear HRec.
                    assert (forall path,
                            list_rel_top eq path_in path ->
                                (exists ind, list_rel is_specialization path ind /\
                                    (List.In (Index (Var v) ind) vars \/
                                    List.In (Var v) vars /\ ind = [::])) -> False) as defined'.
                    {
                        move=> path lrel_top [ind [is_spec LIn]].
                        move: (defined 0 nil path).
                        impl_tac; [> by constructor | idtac ].
                        rewrite cats0; impl_tac; trivial.
                        impl_tac.
                        {
                            do 3 eexists; repeat split.
                            by exact is_spec.
                            by assumption.
                        }
                        {
                            auto.
                        }
                    }
                    clear defined.
                    rewrite <-not_true_iff_false.
                    rewrite generalization_in_soudness.
                    move=> [ind [is_spec' LIn]].
                    inversion is_spec' as [p_nat p_ind p_tl is_spec H0 H1].
                    apply (defined' p_nat).
                    2: by exists ind; split.
                    destruct H0; clear.
                    by induction p_nat; simpl; constructor.
                }
            }
            {
                rewrite find_val_eq; simpl; rewrite eq_Some.
                induction gen_range; simpl.
                by constructor.
                constructor; auto.
                apply HRec.
                2: by rewrite get_typ_of_array_concat; rewrite get_typ_eq; simpl.
                move=> pos path1 path2 is_spec.
                inversion is_spec as [H|]; destruct H; simpl; clear is_spec; rewrite cats0.
                move=> lrel_top def.
                exfalso; move: (defined pos nil path2 (LRnil _)).
                impl_tac.
                {
                    move: lrel_top.
                    clear; move: path2.
                    induction path_in; simpl.
                    by intros; constructor.
                    move=> [|hd2 tl2]; simpl.
                    by intros; constructor.
                    move=> H; constructor; inversion H; auto.
                }
                impl_tac; trivial.
                auto.
            }
        }
        {
            destruct ind as [ae|ae1 ae2|aeL].
            {
                move=> path_in find_soundness defined.
                refine (AccVarInd _ _ _ _ _ _ _ _).
                {
                    clear is_top HRec eqns_type_sound.
                    assert (forall eqns', acc_find_var v path_in eqns tctxt eqns') as H'.
                    2: by auto.
                    move=> eqns'.
                    move: ord defined.
                    induction eqns as [|[vars e] eqns_tl HRec].
                    by constructor.
                    move=> ord defined.
                    apply AccNotFind.
                    {
                        apply (HRec nil); move=> pos path1 path2 is_spec lrel def.
                        move: (defined pos.+1 path1 path2 is_spec lrel def).
                        auto.
                    }
                    {
                        clear HRec.
                        rewrite <-not_true_iff_false.
                        rewrite generalization_in_soudness.
                        move=> [ind [is_spec' LIn]].
                        inversion is_spec' as [p_nat p_ind p_tl is_spec H0 H1].
                        destruct H0; destruct H1; clear is_spec'.
                        destruct (valid_index_imp_exists (IInd ae :: path_tl)) as [path1 is_spec'].
                        by constructor.
                        move: (defined 0 path1 p_nat).
                        impl_tac; trivial.
                        impl_tac.
                        by clear; induction p_nat; simpl; constructor.
                        impl_tac.
                        2: by auto.
                        unfold defined_in; simpl.
                        do 3 eexists; repeat split; trivial.
                        by exact is_spec.
                        auto.
                    }
                }
                {
                    apply HRec.
                    {
                        move: find_soundness; clear.
                        move=> [t [find_eval path_eq]].
                        exists t; split; auto.
                        rewrite get_typ_of_array_concat.
                        destruct get_typ_of_array as [t'|]; auto.
                        destruct t'; simpl in *.
                        all: inversion path_eq; trivial.
                    }
                    move=> pos path1 path2 is_spec lrel_top def.
                    specialize defined with pos (unwrap (eval_arith_expr nil ae) :: path1) path2.
                    rewrite <-app_assoc in lrel_top; simpl in *.
                    exfalso; move: defined; impl_tac.
                    {
                        constructor; auto.
                        constructor.
                        case_eq (eval_arith_expr nil ae); simpl; auto.
                        move=> eval_to_None; unfold eval_to_some in valid_hd.
                        rewrite eval_to_None in valid_hd; discriminate.
                    }
                    impl_tac; trivial.
                    impl_tac; trivial.
                    auto.
                }
            }
            {
                move=> path_in find_soundness defined.
                refine (AccVarRange _ _ _ _ _ _ _ _ _).
                {
                    clear is_top HRec eqns_type_sound.
                    assert (forall eqns', acc_find_var v path_in eqns tctxt eqns') as H'.
                    2: by auto.
                    move=> eqns'.
                    move: ord defined.
                    induction eqns as [|[vars e] eqns_tl HRec].
                    by constructor.
                    move=> ord defined.
                    apply AccNotFind.
                    {
                        apply (HRec nil); move=> pos path1 path2 is_spec lrel def.
                        move: (defined pos.+1 path1 path2 is_spec lrel def).
                        auto.
                    }
                    {
                        clear HRec.
                        rewrite <-not_true_iff_false.
                        rewrite generalization_in_soudness.
                        move=> [ind [is_spec' LIn]].
                        inversion is_spec' as [p_nat p_ind p_tl is_spec H0 H1].
                        destruct H0; destruct H1; clear is_spec'.
                        destruct (valid_index_imp_exists (IRange ae1 ae2 :: path_tl)) as [path1 is_spec'].
                        by constructor.
                        move: (defined 0 path1 p_nat).
                        impl_tac; trivial.
                        impl_tac.
                        by clear; induction p_nat; simpl; constructor.
                        impl_tac.
                        2: by auto.
                        unfold defined_in; simpl.
                        do 3 eexists; repeat split; trivial.
                        by exact is_spec.
                        auto.
                    }
                }
                {
                    move: valid_hd; simpl; move/andP; unfold eval_to_some.
                    case_eq (eval_arith_expr nil ae1).
                    2: by move=> _ [H _]; discriminate.
                    move=> i1 eval1.
                    case_eq (eval_arith_expr nil ae2).
                    2: by move=> _ [_ H]; discriminate.
                    move=> i2 eval2 _; simpl.
                    induction (gen_range_soundness i1 i2) as [|hd tl p_hd p_tl HRec']; simpl.
                    by constructor.
                    constructor; auto.
                    apply HRec.
                    {
                        move: find_soundness; clear.
                        move=> [t [find_eval path_eq]].
                        exists t; split; auto.
                        rewrite get_typ_of_array_concat.
                        destruct get_typ_of_array as [t'|]; auto.
                        destruct t'; simpl in *.
                        all: inversion path_eq; auto.
                    }
                    move=> pos path1 path2 is_spec lrel_top def.
                    exfalso; move: (defined pos (hd :: path1) path2).
                    impl_tac.
                    {
                        constructor; trivial.
                        refine (SpecRange _ _ _ _ _ _ _ _).
                        by exact eval1.
                        by exact eval2.
                        trivial.
                    }
                    impl_tac.
                    {
                        move: lrel_top.
                        unfold eval_arith_expr; simpl.
                        move: (Nat2Z.is_nonneg hd).
                        rewrite Z.le_ngt; move/Z.ltb_spec0.
                        destruct (_ <? _)%Z; simpl; [> by idtac | move=> _ ].
                        rewrite Nat2Z.id; rewrite <-app_assoc; simpl; auto.
                    }
                    impl_tac; trivial.
                    auto.
                }
            }
            {
                move=> path_in find_soundness defined.
                refine (AccVarSlice _ _ _ _ _ _ _ _).
                {
                    clear is_top HRec eqns_type_sound.
                    assert (forall eqns', acc_find_var v path_in eqns tctxt eqns') as H'.
                    2: by auto.
                    move=> eqns'.
                    move: ord defined.
                    induction eqns as [|[vars e] eqns_tl HRec].
                    by constructor.
                    move=> ord defined.
                    apply AccNotFind.
                    {
                        apply (HRec nil); move=> pos path1 path2 is_spec lrel def.
                        move: (defined pos.+1 path1 path2 is_spec lrel def).
                        auto.
                    }
                    {
                        clear HRec.
                        rewrite <-not_true_iff_false.
                        rewrite generalization_in_soudness.
                        move=> [ind [is_spec' LIn]].
                        inversion is_spec' as [p_nat p_ind p_tl is_spec H0 H1].
                        destruct H0; destruct H1; clear is_spec'.
                        destruct (valid_index_imp_exists (ISlice aeL :: path_tl)) as [path1 is_spec'].
                        by constructor.
                        move: (defined 0 path1 p_nat).
                        impl_tac; trivial.
                        impl_tac.
                        by clear; induction p_nat; simpl; constructor.
                        impl_tac.
                        2: by auto.
                        unfold defined_in; simpl.
                        do 3 eexists; repeat split; trivial.
                        by exact is_spec.
                        auto.
                    }
                }
                {
                    simpl in valid_hd; destruct valid_hd as [valid_aeL _].
                    assert (forall (pos : nat) (path1 path2 : seq nat),
                        list_rel is_specialization path1 (ISlice (nil ++ aeL) :: path_tl) ->
                        list_rel_top eq (path_in ++ path1) path2 ->
                        defined_in v path2 pos eqns ->
                            nth 0 ord pos < 0) as defined' by auto.
                    move: defined'; clear defined.
                    destruct find_soundness as [t [find_eq get_typ_soundness]].
                    rewrite find_eq in HRec.
                    assert (match get_typ_of_array path_in t with
                            | Some t' => valid_access t' (ISlice (nil ++ aeL) :: path_tl)
                            | None => False end) as get_typ_soundness' by auto.
                    move: get_typ_soundness'; clear get_typ_soundness.
                    pose (aeL_hd := @nil arith_expr); fold aeL_hd; move: aeL_hd.
                    clear valid_tl.
                    induction valid_aeL as [|ae_hd ae_tl valid_hd valid_tl HRec'].
                    by intros; constructor.
                    move=> aeL_hd get_typ_soundness defined; constructor.
                    {
                        apply HRec.
                        {
                            exists t; split; trivial.  
                            move: get_typ_soundness; clear.
                            rewrite get_typ_of_array_concat.
                            destruct get_typ_of_array as [t'|]; trivial.
                            destruct t'; simpl.
                            all: move=> H; inversion H; trivial.
                        }
                        move=> pos path1 path2 is_spec lrel_top def.
                        unfold eval_to_some in valid_hd.
                        case_eq (eval_arith_expr nil ae_hd).
                        2: by move=> H; rewrite H in valid_hd.
                        rewrite <- app_assoc in lrel_top.
                        move=> i eval_eq; rewrite eval_eq in lrel_top; simpl in lrel_top.
                        exfalso; move: (defined pos (i :: path1) path2); trivial.
                        impl_tac.
                        {
                            constructor; trivial.
                            refine (SpecSlice _ _ _ _ _).
                            2: by exact eval_eq.
                            rewrite List.in_app_iff; simpl; auto.
                        }
                        impl_tac; trivial.
                        impl_tac; trivial.
                        auto.
                    }
                    {
                        apply (HRec' (aeL_hd ++ [:: ae_hd])).
                        all: rewrite <-app_assoc; simpl; auto.
                    }
                }
            }
        }
    }
    {
        move=> v path_tl path_in forall_vindex; move: path_in.
        induction forall_vindex as [|ind path_tl valid_hd valid_tl HRec].
        {
            move=> path_in find_soundness defined.
            destruct find_soundness as [t [find_val_eq get_typ_soundness]].
            case_eq (get_typ_of_array path_in t).
            2: by move=> H; rewrite H in get_typ_soundness.
            clear get_typ_soundness.
            move=> t'; move: path_in defined.
            induction t' as [|d m|t' HRec len].
            all: move=> path_in defined get_typ_eq.
            all: move: (get_len_of_array_to_typ path_in t); rewrite get_typ_eq; simpl.
            all: move=> eq_Some; refine (AccVarFinished _ _ _ _ _ _).
            2,4,6 : rewrite find_val_eq; simpl; rewrite eq_Some; simpl.
            2,3: by constructor.
            {
                refine (termination_proof_ind_lemma _ _ _ _ ord _ _ nil nil _ _ _ _ _).
                {
                    unfold is_topological_sort; destruct is_top; trivial.
                }
                {
                    simpl; reflexivity.
                }
                {
                    simpl.
                    move=> pos path top_eq length_inf.
                    specialize defined with pos nil path.
                    rewrite cats0 in defined; apply defined; trivial.
                    constructor.
                }
                all: simpl; assumption.
            }
            {
                clear find_val_eq HRec_k eqns_type_sound.
                induction gen_range; simpl.
                by constructor.
                constructor; auto.
                apply HRec.
                2: by rewrite get_typ_of_array_concat; rewrite get_typ_eq; simpl.
                move=> pos path1 path2 is_spec.
                inversion is_spec as [H|]; destruct H; simpl; clear is_spec.
                specialize defined with pos nil path2.
                rewrite <-app_assoc; simpl in *.
                move=> lrel_top; apply defined.
                by constructor.
                move: lrel_top.
                clear; move: path2.
                induction path_in; simpl.
                by intros; constructor.
                move=> [|hd2 tl2]; simpl.
                by intros; constructor.
                move=> H; constructor; inversion H; auto.
            }
            {
                refine (termination_proof_ind_lemma _ _ _ _ ord _ _ nil nil _ _ _ _ _).
                {
                    unfold is_topological_sort; destruct is_top; trivial.
                }
                {
                    simpl; reflexivity.
                }
                {
                    simpl.
                    move=> pos path lrel Linf.
                    specialize defined with pos nil path.
                    rewrite cats0 in defined; apply defined; trivial.
                    constructor.
                }
                all: simpl; assumption.
            }
            {
                refine (termination_proof_ind_lemma _ _ _ _ ord _ _ nil nil _ _ _ _ _).
                {
                    unfold is_topological_sort; destruct is_top; trivial.
                }
                {
                    simpl; reflexivity.
                }
                {
                    simpl.
                    move=> pos path lrel linf.
                    specialize defined with pos nil path.
                    rewrite cats0 in defined; apply defined; trivial.
                    constructor.
                }
                all: simpl; assumption.
            }
        }
        {
            destruct ind as [ae|ae1 ae2|aeL].
            {
                move=> path_in type_soundness defined.
                refine (AccVarInd _ _ _ _ _ _ _ _).
                {
                    refine (termination_proof_ind_lemma _ k _ _ ord _ _ nil nil _ _ _ _ _).
                    {
                        unfold is_topological_sort; destruct is_top; trivial.
                    }
                    {
                        simpl; reflexivity.
                    }
                    {
                        simpl.
                        move=> pos path lrel linf.
                        destruct (valid_index_imp_exists _ (Forall_cons _ valid_hd valid_tl)) as [path' is_spec].
                        specialize defined with pos path' path.
                        apply defined; trivial.
                        move: lrel linf; clear.
                        move=> lrel; induction lrel as [l|l|h1 h2 t1 t2 r_hd r_tl HRec]; simpl.
                        {
                            destruct l; simpl.
                            by intro; constructor.
                            intro; exfalso; auto.
                        }
                        {
                            intro; constructor.
                        }
                        {
                            intro; constructor; trivial.
                            apply HRec.
                            apply/leP; apply le_S_n; apply/leP; assumption.
                        }
                    }
                    all: simpl; assumption.
                }
                {
                    apply HRec.
                    {
                        move: type_soundness; clear.
                        move=> [t [-> H]]; eexists; split.
                        by reflexivity.
                        rewrite get_typ_of_array_concat.
                        destruct get_typ_of_array as [t'|].
                        2: destruct H.
                        destruct t'; simpl in *; inversion H; assumption.
                    }
                    move=> pos path1 path2 is_spec.
                    specialize defined with pos (unwrap (eval_arith_expr nil ae) :: path1) path2.
                    rewrite <-app_assoc; simpl in *.
                    apply defined.
                    constructor; auto.
                    constructor.
                    case_eq (eval_arith_expr nil ae); simpl; auto.
                    move=> eval_to_None; unfold eval_to_some in valid_hd.
                    rewrite eval_to_None in valid_hd; discriminate.
                }
            }
            {
                move=> path_in type_soundness defined.
                refine (AccVarRange _ _ _ _ _ _ _ _ _).
                {
                    refine (termination_proof_ind_lemma _ k _ _ ord _ _ nil nil _ _ _ _ _).
                    {
                        unfold is_topological_sort; destruct is_top; trivial.
                    }
                    {
                        simpl; reflexivity.
                    }
                    {
                        simpl.
                        move=> pos path lrel linf.
                        destruct (valid_index_imp_exists _ (Forall_cons _ valid_hd valid_tl)) as [path' is_spec].
                        specialize defined with pos path' path.
                        apply defined; trivial.
                        move: lrel linf; clear.
                        move=> lrel; induction lrel as [l|l|h1 h2 t1 t2 r_hd r_tl HRec]; simpl.
                        {
                            destruct l; simpl.
                            by intro; constructor.
                            intro; exfalso; auto.
                        }
                        {
                            intro; constructor.
                        }
                        {
                            intro; constructor; trivial.
                            apply HRec.
                            apply/leP; apply le_S_n; apply/leP; assumption.
                        }
                    }
                    all: simpl; assumption.
                }
                {
                    move: valid_hd; simpl; move/andP; unfold eval_to_some.
                    case_eq (eval_arith_expr nil ae1).
                    2: by move=> _ [H _]; discriminate.
                    move=> i1 eval1.
                    case_eq (eval_arith_expr nil ae2).
                    2: by move=> _ [_ H]; discriminate.
                    move=> i2 eval2 _; simpl.
                    induction (gen_range_soundness i1 i2) as [|hd tl p_hd p_tl HRec']; simpl.
                    by constructor.
                    constructor; auto.
                    apply HRec.
                    {
                        destruct type_soundness as [t [-> type_soundness]].
                        exists t; split; trivial.
                        rewrite get_typ_of_array_concat.
                        destruct get_typ_of_array as [t'|].
                        2: by destruct type_soundness.
                        destruct t'; simpl in *; inversion type_soundness; trivial.
                    }
                    move=> pos path1 path2 is_spec lrel_top.
                    apply (defined _ (hd :: path1) _).
                    {
                        constructor; trivial.
                        refine (SpecRange _ _ _ _ _ _ _ _).
                        by exact eval1.
                        by exact eval2.
                        trivial.
                    }
                    move: lrel_top.
                    unfold eval_arith_expr; simpl.
                    move: (Nat2Z.is_nonneg hd).
                    rewrite Z.le_ngt; move/Z.ltb_spec0.
                    destruct (_ <? _)%Z; simpl; [> by idtac | move=> _ ].
                    rewrite Nat2Z.id; rewrite <-app_assoc; simpl; auto.
                }
            }
            {
                move=> path_in type_soundness defined.
                refine (AccVarSlice _ _ _ _ _ _ _ _).
                {
                    refine (termination_proof_ind_lemma _ k _ _ ord _ _ nil nil _ _ _ _ _).
                    {
                        unfold is_topological_sort; destruct is_top; trivial.
                    }
                    {
                        simpl; reflexivity.
                    }
                    {
                        simpl.
                        move=> pos path lrel linf.
                        destruct (valid_index_imp_exists _ (Forall_cons _ valid_hd valid_tl)) as [path' is_spec].
                        specialize defined with pos path' path.
                        apply defined; trivial.
                        move: lrel linf; clear.
                        move=> lrel; induction lrel as [l|l|h1 h2 t1 t2 r_hd r_tl HRec]; simpl.
                        {
                            destruct l; simpl.
                            by intro; constructor.
                            intro; exfalso; auto.
                        }
                        {
                            intro; constructor.
                        }
                        {
                            intro; constructor; trivial.
                            apply HRec.
                            apply/leP; apply le_S_n; apply/leP; assumption.
                        }
                    }
                    all: simpl; assumption.
                }
                {
                    simpl in valid_hd; destruct valid_hd as [valid_aeL _].
                    assert (forall (pos : nat) (path1 path2 : seq nat),
                        list_rel is_specialization path1 (ISlice (nil ++ aeL) :: path_tl) ->
                        list_rel_top eq (path_in ++ path1) path2 ->
                        defined_in v path2 pos eqns -> nth k.+1 ord pos < k.+1) as defined'.
                    {
                        simpl; auto.
                    }
                    move: defined'; clear defined.
                    assert (exists t, find_val tctxt v = Some t /\
                        match get_typ_of_array path_in t with
                        | Some t' => valid_access t' (ISlice (nil ++ aeL) :: path_tl)
                        | None => False end) as type_soundness' by refine type_soundness.
                    move: type_soundness'; clear type_soundness.
                    pose (aeL_hd := @nil arith_expr); fold aeL_hd; move: aeL_hd.
                    clear valid_tl.
                    induction valid_aeL as [|ae_hd ae_tl valid_hd valid_tl HRec'].
                    by intros; constructor.
                    move=> aeL_hd type_soundness defined; constructor.
                    {
                        apply HRec.
                        {
                            destruct type_soundness as [t [-> type_soundness]].
                            exists t; split; trivial.
                            rewrite get_typ_of_array_concat; destruct get_typ_of_array as [t'|].
                            2: by destruct type_soundness.
                            destruct t'; simpl in *; inversion type_soundness; trivial.
                        }
                        move=> pos path1 path2 is_spec lrel_top.
                        unfold eval_to_some in valid_hd.
                        case_eq (eval_arith_expr nil ae_hd).
                        2: by move=> H; rewrite H in valid_hd.
                        rewrite <- app_assoc in lrel_top.
                        move=> i eval_eq; rewrite eval_eq in lrel_top; simpl in lrel_top.
                        apply (defined _ (i :: path1)); trivial.
                        constructor; trivial.
                        refine (SpecSlice _ _ _ _ _).
                        2: by exact eval_eq.
                        rewrite List.in_app_iff; simpl; auto.
                    }
                    {
                        apply (HRec' (aeL_hd ++ [:: ae_hd])).
                        all: rewrite <-app_assoc; simpl; auto.
                    }
                }
            }
        }
    }
Qed.

Theorem termination:
    forall tctxt1 tctxt2 eqns ord,
        build_topological_sort (tctxt1 ++ tctxt2) eqns = Some ord ->
        forall v, 
            List.In v (map fst tctxt1) ->
            acc_var v nil nil (tctxt1 ++ tctxt2) eqns.
Proof.
    move=> tctxt1 tctxt2 eqns ord is_top v LIn.
    apply build_topological_sort_soundness in is_top.
    destruct is_top as [is_top eqns_type_sound].
    apply (termination_lemma (list_max ord).+1 _ _ ord).
    1,2: by assumption.
    by constructor.
    {
        move: LIn; clear.
        induction tctxt1 as [|[v' t] tl HRec]; simpl.
        by move=> [].
        move=> [->|LIn].
        {
            rewrite ident_beq_refl.
            eexists; split; [> reflexivity | idtac ].
            destruct t; simpl; trivial.
        }
        {
            destruct ident_beq.
            {
                eexists; split; [> reflexivity | idtac ].
                destruct t; simpl; trivial.    
            }
            destruct (HRec LIn) as [t' [-> H]].
            eexists; split; [> reflexivity | idtac ].
            destruct t'; simpl; trivial.
        }
    }
    {
        move=> pos path1 path2 _ _ defined.
        assert (pos < length eqns) as HInf.
        {
            unfold defined_in in defined.
            destruct defined as [vL [e [ind [nth_err _]]]].
            apply/ltP.
            rewrite <-nth_error_Some.
            move=> H; rewrite H in nth_err.
            inversion nth_err.
        }
        move: HInf.
        destruct is_top as [-> _].
        clear.
        move: (Nat.le_refl (list_max ord)); rewrite list_max_le.
        pose (maxi := list_max ord); fold maxi; move: pos maxi.
        induction ord as [|hd tl HRec]; simpl.
        by auto.
        move=> [|pos] maxi all_inf HInf; simpl.
        all: inversion all_inf.
        {
            apply/ltP.
            refine (Nat.lt_le_trans _ _ _ (Nat.lt_succ_diag_r _) _).
            apply le_n_S; assumption.
        }
        apply HRec; trivial.
    }
Qed.

Definition expr_head e := match e with | ECons h _ => h | _ => Tuple Enil end.

Definition acc_pred_inv_hd {tctxt eqns hd tl} (a : acc_pred_l tctxt eqns (ECons hd tl)) : acc_pred tctxt eqns hd :=
    match a in (acc_pred_l tctxt eqns e) return e = ECons hd tl -> acc_pred tctxt eqns (expr_head e)
    with
    | AccEnil _ _ => fun HEq =>
        match eq_ind Enil (fun e => match e with Enil => True | ECons _ _ => False end) I _ HEq with end
    | AccECons _ _ _ _ a _ =>  fun _ => a
    end Logic.eq_refl.

Definition expr_tail e := match e with | ECons _ t => t | _ => e end.

Definition acc_pred_inv_tl {tctxt eqns hd tl} (a : acc_pred_l tctxt eqns (ECons hd tl)) : acc_pred_l tctxt eqns tl :=
    match a in (acc_pred_l tctxt eqns e) return e = ECons hd tl -> acc_pred_l tctxt eqns (expr_tail e)
    with
    | AccEnil _ _ => fun HEq =>
        match eq_ind Enil (fun e => match e with Enil => True | ECons _ _ => False end) I _ HEq with end
    | AccECons _ _ _ _ _ a => fun _ => a
    end Logic.eq_refl.

Definition expr_inv_not e := match e with | Not e => e | _ => e end.

Definition acc_pred_inv_Not {tctxt eqns e} (a : acc_pred tctxt eqns (Not e)) : acc_pred tctxt eqns e :=
    match a in (acc_pred tctxt eqns e') return Not e = e' -> acc_pred tctxt eqns (expr_inv_not e')
    with
    | AccNot _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (Not _) (fun e => match e with Not _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition expr_inv_Shift e := match e with | Shift _ e _ => e | _ => e end.

Definition acc_pred_inv_Shift {tctxt eqns sop e ae} (a : acc_pred tctxt eqns (Shift sop e ae)) : acc_pred tctxt eqns e :=
    match a in (acc_pred tctxt eqns e') return Shift sop e ae = e' -> acc_pred tctxt eqns (expr_inv_Shift e')
    with
    | AccShift _ _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (Shift _ _ _) (fun e => match e with Shift _ _ _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition expr_inv_Arith_1 e := match e with | Arith _ e _ => e | _ => e end.
Definition expr_inv_Arith_2 e := match e with | Arith _ _ e => e | _ => e end.
Definition expr_inv_Log_1 e := match e with | Log _ e _ => e | _ => e end.
Definition expr_inv_Log_2 e := match e with | Log _ _ e => e | _ => e end.

Definition acc_pred_inv_Arith_1 {tctxt eqns aop e1 e2} (a : acc_pred tctxt eqns (Arith aop e1 e2)) : acc_pred tctxt eqns e1 :=
    match a in (acc_pred tctxt eqns e') return Arith aop e1 e2 = e' -> acc_pred tctxt eqns (expr_inv_Arith_1 e')
    with
    | AccAop _ _ _ _ _ a _ => fun _ => a
    | _ => fun HEq =>
        match eq_ind (Arith _ _ _) (fun e => match e with Arith _ _ _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_pred_inv_Arith_2 {tctxt eqns aop e1 e2} (a : acc_pred tctxt eqns (Arith aop e1 e2)) : acc_pred tctxt eqns e2 :=
    match a in (acc_pred tctxt eqns e') return Arith aop e1 e2 = e' -> acc_pred tctxt eqns (expr_inv_Arith_2 e')
    with
    | AccAop _ _ _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (Arith _ _ _) (fun e => match e with Arith _ _ _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_pred_inv_Log_1 {tctxt eqns sop e1 e2} (a : acc_pred tctxt eqns (Log sop e1 e2)) : acc_pred tctxt eqns e1 :=
    match a in (acc_pred tctxt eqns e') return Log sop e1 e2 = e' -> acc_pred tctxt eqns (expr_inv_Log_1 e')
    with
    | AccLop _ _ _ _ _ a _ => fun _ => a
    | _ => fun HEq =>
        match eq_ind (Log _ _ _) (fun e => match e with Log _ _ _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_pred_inv_Log_2 {tctxt eqns sop e1 e2} (a : acc_pred tctxt eqns (Log sop e1 e2)) : acc_pred tctxt eqns e2 :=
    match a in (acc_pred tctxt eqns e') return Log sop e1 e2 = e' -> acc_pred tctxt eqns (expr_inv_Log_2 e')
    with
    | AccLop _ _ _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (Log _ _ _) (fun e => match e with Log _ _ _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition expr_inv_toList e := match e with
    | Tuple el => el
    | BuildArray el => el
    | Fun _ el => el
    | Fun_v _ _ el => el
    | _ => Enil end.

Definition acc_pred_inv_Tuple {tctxt eqns el} (a : acc_pred tctxt eqns (Tuple el)) : acc_pred_l tctxt eqns el :=
    match a in (acc_pred tctxt eqns e) return Tuple el = e -> acc_pred_l tctxt eqns (expr_inv_toList e)
    with
    | AccTuple _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (Tuple _) (fun e => match e with Tuple _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_pred_inv_BuildArray {tctxt eqns el} (a : acc_pred tctxt eqns (BuildArray el)) : acc_pred_l tctxt eqns el :=
    match a in (acc_pred tctxt eqns e) return BuildArray el = e -> acc_pred_l tctxt eqns (expr_inv_toList e)
    with
    | AccBuildArray _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (BuildArray _) (fun e => match e with BuildArray _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_pred_inv_Fun {tctxt eqns v el} (a : acc_pred tctxt eqns (Fun v el)) : acc_pred_l tctxt eqns el :=
    match a in (acc_pred tctxt eqns e) return Fun v el = e -> acc_pred_l tctxt eqns (expr_inv_toList e)
    with
    | AccFun _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (Fun _ _) (fun e => match e with Fun _ _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_pred_inv_Fun_v {tctxt eqns v ae el} (a : acc_pred tctxt eqns (Fun_v v ae el)) : acc_pred_l tctxt eqns el :=
    match a in (acc_pred tctxt eqns e) return Fun_v v ae el = e -> acc_pred_l tctxt eqns (expr_inv_toList e)
    with
    | AccFun_v _ _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (Fun_v _ _ _) (fun e => match e with Fun_v _ _ _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition expr_inv_var v :=
    match v with
    | ExpVar (Var v) => v
    | ExpVar (Index (Var v) _) => v
    | _ => Num 0
    end.

Definition acc_pred_inv_Var {tctxt eqns v} (a : acc_pred tctxt eqns (ExpVar (Var v))) : acc_var v nil nil tctxt eqns :=
    match a in acc_pred tctxt eqns e return ExpVar (Var v) = e -> acc_var (expr_inv_var e) nil nil tctxt eqns
    with
    | AccExpVar _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (ExpVar (Var _)) (fun e => match e with ExpVar (Var _) => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition expr_inv_var_ind v :=
    match v with
    | ExpVar (Index _ i) => i
    | _ => nil
    end.

Definition acc_pred_inv_Var_Ind {tctxt eqns v ind} (a : acc_pred tctxt eqns (ExpVar (Index (Var v) ind))) : acc_var v nil ind tctxt eqns :=
    match a in acc_pred tctxt eqns e return ExpVar (Index (Var v) ind) = e -> acc_var (expr_inv_var e) nil (expr_inv_var_ind e) tctxt eqns
    with
    | AccExpVarInd _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (ExpVar (Index (Var _) _)) (fun e => match e with ExpVar (Index (Var _) _) => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_var_inv_find {v path_in path_tl tctxt eqns} (acc : acc_var v path_in path_tl tctxt eqns) : acc_find_var v path_in eqns tctxt eqns :=
    match acc in acc_var v' path_in' path_tl' tctxt eqns' return acc_find_var v' path_in' eqns' tctxt eqns' with
    | AccVarInd   _ _ _ _ _ _ a _ => a
    | AccVarSlice _ _ _ _ _ _ a _ => a
    | AccVarRange _ _ _ _ _ _ _ a _ => a
    | AccVarFinished _ _ _ _ a _ => a
    end.

Definition list_tl {A} (t : list A) := match t with | _ :: t => t | _ => t end.

Definition inv_IInd_hd t := match t with IInd ae :: _ => ae | _ => Var_e (Num 0) end.

Definition inv_ISlice_l t := match t with ISlice aeL :: _ => aeL | _ => nil end.

Definition inv_IRange_l t := match t with IRange ae1 ae2 :: _ => [seq Const_e (Z.of_nat i) | i <- gen_range (unwrap (eval_arith_expr nil ae1)) (unwrap (eval_arith_expr nil ae2))] | _ => nil end.

Definition acc_var_inv_Ind_rec {v path_in path_tl tctxt eqns ae} (acc : acc_var v path_in (IInd ae::path_tl) tctxt eqns)
    : acc_var v (path_in ++ [:: unwrap (eval_arith_expr nil ae)]) path_tl tctxt eqns :=
    match acc in acc_var v' p_in' p_tl' tctxt' eqns' return IInd ae :: path_tl = p_tl' ->
        acc_var v' (p_in' ++ [:: unwrap (eval_arith_expr nil (inv_IInd_hd p_tl'))]) (list_tl p_tl') tctxt' eqns' with
    | AccVarInd _ _ _ _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (IInd _ :: _ ) (fun e => match e with IInd _ :: _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_Var_inv_Slice_rec {v path_in path_tl eqns tctxt aeL} (acc : acc_var v path_in (ISlice aeL::path_tl) tctxt eqns)
    : acc_forall v path_in path_tl tctxt eqns aeL :=
    match acc in acc_var v' p_in' p_tl' tctxt' eqns'
    return ISlice aeL :: path_tl = p_tl' -> acc_forall v' p_in' (list_tl p_tl') tctxt' eqns' (inv_ISlice_l p_tl')
    with
    | AccVarSlice _ _ _ _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (ISlice _ :: _) (fun e => match e with ISlice _ :: _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_Var_inv_Range_rec {v path_in path_tl tctxt eqns ae1 ae2} (acc : acc_var v path_in (IRange ae1 ae2::path_tl) tctxt eqns)
    : acc_forall v path_in path_tl tctxt eqns [seq Const_e (Z.of_nat i) | i <- gen_range (unwrap (eval_arith_expr nil ae1)) (unwrap (eval_arith_expr nil ae2))] :=
    match acc in acc_var v' p_in' p_tl' tctxt eqns'
    return IRange ae1 ae2 :: path_tl = p_tl' -> acc_forall v' p_in' (list_tl p_tl') tctxt eqns' (inv_IRange_l p_tl')
    with
    | AccVarRange _ _ _ _ _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind (IRange _ _ :: _) (fun e => match e with IRange _ _ :: _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_Var_inv_Typ {v path_in tctxt eqns} (acc : acc_var v path_in nil tctxt eqns)
    : acc_forall v path_in nil tctxt eqns [seq Const_e (Z.of_nat i) | i <- gen_range' (omap (get_len_of_array path_in) (find_val tctxt v))] :=
    match acc in acc_var v' p_in' p_tl' tctxt' eqns' 
    return nil = p_tl' -> acc_forall v' p_in' nil tctxt' eqns' [seq Const_e (Z.of_nat i) | i <- gen_range' (omap (get_len_of_array p_in') (find_val tctxt' v'))]
    with
    | AccVarFinished _ _ _ _ _ a => fun _ => a
    | _ => fun HEq =>
        match eq_ind nil (fun l => match l with nil => True | _ :: _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition acc_forall_inv_tail {v path_in path_tl tctxt eqns ae_hd ae_tl} (H : acc_forall v path_in path_tl tctxt eqns (ae_hd :: ae_tl))
    : acc_forall v path_in path_tl tctxt eqns ae_tl :=
    match H in acc_forall _ _ _ _ _ l
    return ae_hd :: ae_tl = l -> acc_forall _ _ _ _ _ (list_tl l) with
    | AccForallCons _ _ _ _ _ _ _ _ H' => fun _ => H'
    | AccForallNil _ _ _ _ _ => fun HEq =>
        match eq_ind (_ :: _) (fun e => match e with _ :: _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition list_ae_head l :=
    match l with
    | hd :: _ => hd
    | nil => Var_e (Num 0)
    end.

Definition acc_forall_inv_head {v path_in path_tl tctxt eqns ae_hd ae_tl} (H : acc_forall v path_in path_tl tctxt eqns (ae_hd :: ae_tl))
    : acc_var v (path_in ++ [:: unwrap (eval_arith_expr nil ae_hd)]) path_tl tctxt eqns :=
    match H in acc_forall v' p_in' p_tl' tctxt' eqns' l
    return ae_hd :: ae_tl = l -> acc_var v' (p_in' ++ [:: unwrap (eval_arith_expr nil (list_ae_head l))]) p_tl' tctxt' eqns' with
    | AccForallCons _ _ _ _ _ _ _ H' _ => fun _ => H'
    | AccForallNil _ _ _ _ _ => fun HEq =>
        match eq_ind (_ :: _) (fun e => match e with _ :: _ => True | _ => False end) I _ HEq with end
    end Logic.eq_refl.

Definition list_head_1 (el : list (list var * expr)) :=
    match el with
    | (vL, _) :: _ => vL
    | nil => nil
    end.

Definition acc_find_var_inv_tl {v path vL e eqns_tl tctxt eqns} (acc : acc_find_var v path ((vL, e) :: eqns_tl) tctxt eqns)
    : generalization_in v path vL = false -> acc_find_var v path eqns_tl tctxt eqns :=
    match acc in acc_find_var v path e_tl tctxt' eqns'
    return (vL, e) :: eqns_tl = e_tl -> generalization_in v path (list_head_1 e_tl) = false -> acc_find_var v path (list_tl e_tl) tctxt' eqns' with
    | AccFindIn _ _ _ _ _ _ _ _ HEq' => fun _ HEq =>
        match eq_ind true (fun t => match t with true => True | false => False end) I _ (Logic.eq_trans (Logic.eq_sym HEq') HEq) with end
    | AccFindNil _ _ _ _ => fun HAbs _ =>
        match eq_ind (_ :: _) (fun l => match l with _ :: _ => True | nil => False end) I _ HAbs with end
    | AccNotFind _ _ _ _ _ _ _ a _ => fun _ _ => a
    end Logic.eq_refl.

Definition list_expr_hd (el : list (list var * expr)) :=
    match el with
    | (_, e) :: _ => e
    | nil => Const 0 None
    end.

Definition acc_find_var_inv_hd {v path vL e eqns_tl tctxt eqns} (acc : acc_find_var v path ((vL, e) :: eqns_tl) tctxt eqns)
    : generalization_in v path vL = true -> acc_pred tctxt eqns e :=
    match acc in acc_find_var v path e_tl tctxt' eqns'
    return (vL, e) :: eqns_tl = e_tl -> generalization_in v path (list_head_1 e_tl) = true -> acc_pred tctxt' eqns' (list_expr_hd e_tl) with
    | AccNotFind _ _ _ _ _ _ _ _ HEq' => fun _ HEq =>
        match eq_ind true (fun t => match t with true => True | false => False end) I _ (Logic.eq_trans (Logic.eq_sym HEq) HEq') with end
    | AccFindNil _ _ _ _ => fun HAbs _ =>
        match eq_ind (_ :: _) (fun l => match l with _ :: _ => True | nil => False end) I _ HAbs with end
    | AccFindIn _ _ _ _ _ _ _ a _ => fun _ _ => a
    end Logic.eq_refl.

Fixpoint get_typ typ (path : list indexing) :=
    match path with
    | nil => Some (typ, 1)
    | ind :: path =>
        match typ with
        | Array typ _ =>
            (typ, len) <- get_typ typ path;
            match ind with
            | IInd _ => Some (typ, len)
            | ISlice indL => Some (typ, len * length indL)
            | IRange ae1 ae2 =>
                i1 <- eval_arith_expr nil ae1;
                i2 <- eval_arith_expr nil ae2;
                Some (typ, len * ((1 + Nat.max i1 i2) - Nat.min i1 i2))
            end
        | _ => None
        end
    end.

Fixpoint get_length typ :=
    match typ with
    | Array typ len => len * get_length typ
    | _ => 1
    end.

Fixpoint get_typ_dir typ :=
    match typ with
    | Array typ _ => get_typ_dir typ
    | Nat => None
    | Uint Hslice (Mint n) => Some (DirH n)
    | Uint Hslice _ => None
    | Uint Vslice (Mint n) => Some (DirV n)
    | Uint Vslice _ => None
    | Uint Bslice _ => Some DirB
    | Uint Natdir _ | Uint (Varslice _) _ | Uint (Mslice _) _ => None
    end.

Definition skip_value (typ : typ) (nb_times : nat) (vals : list cst_or_int) : option (list cst_or_int) :=
    d <- get_typ_dir typ;
    (_, vals) <- build_ctxt_aux_take_n (nb_times * get_length typ) vals d;
    Some vals.

Fixpoint build_value (typ : typ) (path_ind : list indexing) (path_nat : list nat) (vals : list cst_or_int) : option (@cst_or_int Z) :=
    match path_ind with
    | nil =>
        None (* TODO *)
    | IInd _ :: pind_tl =>
        match path_nat with
        | nil => None
        | _ :: pnat_tl =>
            match typ with
            | Array typ' _ =>
                build_value typ' pind_tl pnat_tl vals
            | _ => None
            end
        end
    | IRange ae1 ae2 :: pind_tl =>
        i1 <- eval_arith_expr nil ae1;
        i2 <- eval_arith_expr nil ae2;
        match path_nat with
        | nil => None
        | pos :: pnat_tl =>
            match typ with
            | Array typ' _ =>
                (_, ress) <- fold_left (fun opt i =>
                    match opt with
                    | Some (vals, None) =>
                        if Nat.eqb pos i
                        then
                            ress' <- build_value typ' pind_tl pnat_tl vals;
                            Some (vals, Some ress')
                        else
                            vals <- skip_value typ' 1 vals;
                            Some (vals, None)
                    | _ => opt
                    end) (gen_range i1 i2) (Some (vals, None));
                ress
            | _ => None
            end
        end
    | ISlice indL :: pind_tl =>
        match path_nat with
        | nil => None
        | pos :: pnat_tl =>
            match typ with
            | Array typ' _ =>
                (_, ress) <- fold_left (fun opt ae =>
                    match opt with
                    | Some (vals, None) =>
                        if eval_to_nat pos ae
                        then
                            ress' <- build_value typ' pind_tl pnat_tl vals;
                            Some (vals, Some ress')
                        else
                            vals <- skip_value typ' 1 vals;
                            Some (vals, None)
                    | _ => opt
                    end) indL (Some (vals, None));
                ress
            | _ => None
            end
        end
    end.

Fixpoint extract_val (vL : list var) (v : ident) (path : list nat) (tctxt : list (ident * typ)) (vals : list cst_or_int) : option cst_or_int :=
    match vL with
    | nil => None
    | var :: vL =>
        if is_generalization v path var
        then
            typ <- find_val tctxt v;
            path' <- match var with
                | Var _ => Some nil
                | Index (Var _) ind => Some ind
                | _ => None
            end;
            build_value typ path' path vals
        else
            (v', path') <- match var with
                | Var v' => Some (v', nil)
                | Index (Var v') ind => Some (v', ind)
                | _ => None
            end;
            typ <- find_val tctxt v';
            (typ, len) <- get_typ typ path';
            vals <- skip_value typ len vals;
            extract_val vL v path tctxt vals
    end.


(** We assert that `length values = prod_list dim` *)
Fixpoint get_access (values : list Z) (acc : access) (dim : list nat) : option (list Z * list nat) :=
    match acc with
    | AAll => Some (values, dim)
    | ASlice nil _ => None
    | AInd i acc_tl =>
        match dim with
        | nil => None
        | d::dim_tl =>
            if length values mod d =? 0
            then
                l' <- split_into_segments d (length values / d) values;
                v <- nth_error l' i;
                get_access v acc_tl dim_tl
            else
                None
        end
    | ASlice indices acc_tl =>
        match dim with
        | nil =>
            None
        | d::dim_tl =>
            if length values mod d =? 0
            then
                l' <- split_into_segments d (length values / d) values;
                (l', dim') <- fold_right (fun v l => (l', _) <- l; v' <- v; (v'', dim') <- get_access v' acc_tl dim_tl; Some (v'' ++ l', dim'))
                        (Some (nil, nil)) (map (fun i => nth_error l' i) indices);
                Some (l', length indices::dim')
            else None (** Assertion not verified *)
        end
    end.

  
Fixpoint eval_expr (arch : architecture) (eqns : list (list var * expr))
        (tctxt : list (ident * typ)) (args : list (ident * cst_or_int)) (e : expr)
        (a : acc_pred tctxt eqns e) {struct a} : option Value :=
    match e return acc_pred tctxt eqns e -> option (Value) with
    | Const n None => fun _ => Some (CoIL n::nil)
    | Const n (Some typ) => fun _ => build_integer typ n
    | ExpVar (Var v) => fun acc =>
        match find_val args v with
        | Some val => Some [:: val]
        | None =>
            v <- eval_var arch eqns tctxt args v nil nil (acc_pred_inv_Var acc);
            Some [:: v]
        end
    | ExpVar (Index (Var v) ind) => fun acc =>
        match find_val args v with
        | Some val => 
            acc <- access_of_ind nil ind;
            match val with
            | CoIL _ => None
            | CoIR d v form =>
                (v,f) <- get_access v acc form;
                Some [:: CoIR d v f]
            end
        | None =>
            v <- eval_var arch eqns tctxt args v nil ind (acc_pred_inv_Var_Ind acc);
            Some [:: v]
        end
    | ExpVar _ => fun _ => None
    | Tuple el => fun acc =>
        eval_list_expr arch eqns tctxt args el (acc_pred_inv_Tuple acc)
    | BuildArray el => fun acc =>
        vl <- eval_list_expr' arch eqns tctxt args el (acc_pred_inv_BuildArray acc);
        (nb, vals, form, d) <- vl;
        Some (CoIR d vals (nb :: form) :: nil)
    | Not e => fun acc =>
        v <- eval_expr arch eqns tctxt args e (acc_pred_inv_Not acc);
        eval_monop (arith_wrapper (IMPL_LOG arch) lnot) v
    | Arith aop e1 e2 => fun acc =>
        v1 <- eval_expr arch eqns tctxt args e1 (acc_pred_inv_Arith_1 acc);
        v2 <- eval_expr arch eqns tctxt args e2 (acc_pred_inv_Arith_2 acc);
        let f := match aop with
            | Add => arith_wrapper (IMPL_ARITH arch) add_fun
            | Sub => arith_wrapper (IMPL_ARITH arch) sub_fun
            | Div => arith_wrapper (IMPL_ARITH arch) div_fun
            | Mod => arith_wrapper (IMPL_ARITH arch) mod_fun
            | Mul => arith_wrapper (IMPL_ARITH arch) mul_fun
        end
        in eval_binop f v1 v2
    | Log lop e1 e2 => fun acc =>
        v1 <- eval_expr arch eqns tctxt args e1 (acc_pred_inv_Log_1 acc);
        v2 <- eval_expr arch eqns tctxt args e2 (acc_pred_inv_Log_2 acc);
        f <- match lop with
            | And | Masked And =>   Some (arith_wrapper (IMPL_LOG arch) land)
            | Or | Masked Or =>     Some (arith_wrapper (IMPL_LOG arch) lor)
            | Xor | Masked Xor =>   Some (arith_wrapper (IMPL_LOG arch) lxor)
            | Andn | Masked Andn => Some (arith_wrapper (IMPL_LOG arch) landn)
            | Masked (Masked _) => None
        end;
        eval_binop f v1 v2
    | Shift sop e ae => fun acc =>
        v1 <- eval_expr arch eqns tctxt args e (acc_pred_inv_Shift acc);
        v2 <- eval_arith_expr nil ae;
        eval_shift arch sop v1 v2
    | Bitmask _ _ => fun _ => None
    | Pack _ _ _ => fun _ => None
    | Shuffle _ _ => fun _ => None
    | Fun v el => fun acc =>
        vl <- eval_list_expr arch eqns tctxt args el (acc_pred_inv_Fun acc);
        None
    | Fun_v v ae el => fun acc =>
        vl <- eval_list_expr arch eqns tctxt args el (acc_pred_inv_Fun_v acc);
        None
    end a
with eval_list_expr (arch : architecture) (eqns : list (list var * expr)) (tctxt : list (ident * typ))
        (args : list (ident * cst_or_int)) (el : expr_list) (a : acc_pred_l tctxt eqns el) {struct a}
            : option Value :=
    match el return acc_pred_l tctxt eqns el -> option Value with
    | Enil => fun _ => Some nil
    | ECons hd tl => fun acc =>
        hd <- eval_expr arch eqns tctxt args hd (acc_pred_inv_hd acc);
        tl <- eval_list_expr arch eqns tctxt args tl (acc_pred_inv_tl acc);
        Some (linearize_list_value hd tl)
    end a
with eval_list_expr' (arch : architecture) (eqns : list (list var * expr)) (tctxt : list (ident * typ))
        (args : list (ident * cst_or_int)) (el : expr_list) (a : acc_pred_l tctxt eqns el) {struct a}
            : option (option (nat * list Z * list nat * dir)) :=
    match el return acc_pred_l tctxt eqns el -> option (option (nat * list Z * list nat * dir)) with
    | Enil => fun _ => Some None
    | ECons hd tl => fun acc =>
        hd <- eval_expr arch eqns tctxt args hd (acc_pred_inv_hd acc);
        tl <- eval_list_expr' arch eqns tctxt args tl (acc_pred_inv_tl acc);
        match hd with
        | CoIR d v form::nil =>
            match tl with
            | None => Some (Some (1, v, form, d))
            | Some (l, v', form', d') =>
                if dir_beq d d' && list_beq nat Nat.eqb form form'
                then
                    Some (Some (l + 1, v ++ v', form', d'))
                else
                    None
            end
        | _ => None
        end
    end a
with eval_var_find (eqns eqns': list (list var * expr)) (arch : architecture)
        (tctxt : list (ident * typ)) (args : list (ident * cst_or_int)) (v : ident)
        (path : list nat) (a : acc_find_var v path eqns' tctxt eqns) {struct a}
            : option (option cst_or_int) :=
    match eqns' return acc_find_var v path eqns' tctxt eqns -> option (option cst_or_int) with
    | nil => fun acc => None
    | (vL, e) :: eqns_tl => fun acc =>
        match generalization_in v path vL as g
        return generalization_in v path vL = g -> option (option cst_or_int)
        with
        | true => fun HEq =>
            match eval_expr arch eqns tctxt args e (acc_find_var_inv_hd acc HEq) with
            | Some val =>
                Some (extract_val vL v path tctxt val)
            | None => Some None
            end
        | false => fun HEq =>
            eval_var_find eqns eqns_tl arch tctxt args v path (acc_find_var_inv_tl acc HEq)
        end Logic.eq_refl
    end a
with eval_var (arch : architecture) (eqns : list (list var * expr)) (tctxt : list (ident * typ))
        (args : list (ident * cst_or_int)) (v : ident) (path_in : list nat) (path_tl : list indexing)
        (a : acc_var v path_in path_tl tctxt eqns) {struct a} : option cst_or_int :=
    match eval_var_find eqns eqns arch tctxt args v path_in (acc_var_inv_find a) with
    | None => match path_tl return acc_var v path_in path_tl tctxt eqns -> option cst_or_int with
        | nil => fun acc =>
            match find_val tctxt v as ot
            return acc_forall v path_in nil tctxt eqns [seq Const_e (Z.of_nat i) | i <- gen_range' (omap (get_len_of_array path_in) ot)] -> option _
            with
            | None => fun=>None
            | Some t =>
                match get_len_of_array path_in t as oi
                return acc_forall v path_in nil tctxt eqns [seq Const_e (Z.of_nat i) | i <- gen_range' (Some oi)] -> option _
                with
                | None => fun=> None
                | Some len => fun acc' =>
                    if len =? 0
                    then
                        None
                    else
                        t <- eval_var_slice arch eqns tctxt args v path_in nil
                            [seq Const_e (Z.of_nat i) | i <- gen_range 0 (len - 1)] acc';
                        (dir, val, form, nb) <- t;
                        Some (CoIR dir val (nb :: form))
                end
            end (acc_Var_inv_Typ acc)
        | IInd ae :: path_tl' => fun acc =>
            match eval_arith_expr nil ae as oi
            return acc_var v (path_in ++ [:: unwrap oi]) path_tl' tctxt eqns -> option cst_or_int
            with
            | Some i => fun acc' =>
                eval_var arch eqns tctxt args v (path_in ++ [:: i]) path_tl' acc'
            | None => fun _ => None
            end (acc_var_inv_Ind_rec acc)
        | ISlice aeL :: path_tl' => fun acc =>
            t <- eval_var_slice arch eqns tctxt args v path_in path_tl' aeL (acc_Var_inv_Slice_rec acc);
            (dir, val, form, nb) <- t;
            Some (CoIR dir val (nb :: form))
        | IRange ae1 ae2 :: path_tl' => fun acc =>
            match eval_arith_expr nil ae1 as oi1
            return acc_forall v path_in path_tl' tctxt eqns [seq Const_e (Z.of_nat i) | i <- gen_range (unwrap oi1) (unwrap (eval_arith_expr nil ae2))] -> option _
            with
            | Some i1 =>
                match eval_arith_expr nil ae2 as oi2
                return acc_forall v path_in path_tl' tctxt eqns [seq Const_e (Z.of_nat i) | i <- gen_range i1 (unwrap oi2)] -> option _
                with
                | Some i2 => fun acc' =>
                    t <- eval_var_slice arch eqns tctxt args v path_in path_tl'
                        [seq Const_e (Z.of_nat i) | i <- gen_range i1 i2] acc';
                    (dir, val, form, nb) <- t;
                    Some (CoIR dir val (nb :: form))
                | None => fun _ => None
                end
            | None => fun _ => None
            end (acc_Var_inv_Range_rec acc)
        end a
    | Some None => None
    | Some (Some v) =>
        acc <- access_of_ind nil path_tl;
        match v with
        | CoIL _ => None
        | CoIR d v form =>
            (v,f) <- get_access v acc form;
            Some (CoIR d v f)
        end
    end
with eval_var_slice (arch : architecture) (eqns : list (list var * expr)) (tctxt : list (ident * typ))
    (args : list (ident * cst_or_int))
    (v : ident) (path_in : list nat) (path_tl : list indexing) (aeL : list arith_expr)
    (a : acc_forall v path_in path_tl tctxt eqns aeL)
    {struct a} : option (option (dir * list Z * list nat * nat)) :=
    match aeL
    return acc_forall v path_in path_tl tctxt eqns aeL -> _ with
    | nil => fun _ => Some None
    | ae_hd :: ae_tl => fun acc =>
        tl <- eval_var_slice arch eqns tctxt args v path_in path_tl ae_tl (acc_forall_inv_tail acc);
        match eval_arith_expr nil ae_hd as oi
        return acc_var v (path_in ++ [:: unwrap oi]) path_tl tctxt eqns -> _
        with
        | Some i => fun acc' =>
            v <- eval_var arch eqns tctxt args v (path_in ++ [:: i]) path_tl acc';
            match tl with
            | None =>
                match v with
                | CoIR d v f => Some (Some (d, v, f, 1))
                | _ => None
                end
            | Some (dir, values, form, size) =>
                match v with
                | CoIR d v f =>
                    if dir_beq dir d && list_beq nat Nat.eqb form f
                    then
                        Some (Some (dir, v ++ values, form, size + 1))
                    else None
                | _ => None
                end
            end
        | None => fun _ => None
        end (acc_forall_inv_head acc)
    end a
.

Definition proj_types (p : var_d) : ident * typ := (VD_ID p, VD_TYP p).

Lemma proj_term_tl:
    forall tctxt eqns hd tl,
        (forall v, List.In v (hd :: tl) -> acc_var v nil nil tctxt eqns) ->
        (forall v, List.In v tl -> acc_var v nil nil tctxt eqns).
Proof.
    move=> tctxt eqns hd tl H v LIn; apply H.
    simpl; right; assumption.
Qed.

Lemma proj_term_hd:
    forall tctxt eqns hd tl,
        (forall v, List.In v (hd :: tl) -> acc_var v nil nil tctxt eqns) ->
        acc_var hd nil nil tctxt eqns.
Proof.
    move=> tctxt eqns hd tl H; apply H.
    simpl; left; reflexivity.
Qed.

Fixpoint eval_vars arch tctxt args eqns out_vars : (forall v, List.In v out_vars -> acc_var v nil nil tctxt eqns) -> option (list cst_or_int) :=
    match out_vars with
    | nil => fun=> Some nil
    | v::tl =>
        fun acc_pred =>
            v <- eval_var arch eqns tctxt args v nil nil (proj_term_hd _ _ _ _ acc_pred);
            v_tl <- eval_vars arch tctxt args eqns tl (proj_term_tl _ _ _ _ acc_pred);
            Some (linearize_list_value (v :: nil) v_tl)
    end.

Fixpoint build_ctxt_aux_take_n (nb : nat) (input : list (@cst_or_int Z)) (d : dir) : option (list Z * list (@cst_or_int Z)) :=
    match nb with
    | 0 => Some (nil, input)
    | S nb' => match input with
        | nil => None
        | (CoIL n)::in_tl =>
            (out, rest) <- build_ctxt_aux_take_n nb' in_tl d;
            Some (n::out, rest)
        | (CoIR d' iL _)::in_tl =>
            if dir_beq d d'
            then
                let (hd, tl) := try_take_n nb iL in
                match tl with
                | SumR nil => Some (hd, in_tl)
                | SumR tl => Some(hd, CoIR d' tl (length tl::nil)::in_tl)
                | SumL nb =>
                    (out, rest) <- build_ctxt_aux_take_n nb in_tl d;
                    Some (hd ++ out, rest)
                end
            else None
        end
    end.

Fixpoint build_ctxt_aux (typ : typ) (input : list (@cst_or_int Z)) (l : list nat) : option (@cst_or_int Z * list (@cst_or_int Z)) :=
    match typ with
    | Nat => match input with
        | CoIL n :: input' => Some (CoIL n, input') 
        | _ => None
        end
    | Uint d (Mint n) =>
        annot <- IntSize_of_nat n;
        d <- match d with
            | Hslice => Some (DirH annot)
            | Vslice => Some (DirV annot)
            | Bslice => Some DirB
            | _ => None
        end;
        (valL, input') <- build_ctxt_aux_take_n (prod_list l) input d;
        Some (CoIR d valL l, input')
    | Uint _ Mnat => None
    | Uint _ (Mvar _) => None
    | Array typ len =>
        build_ctxt_aux typ input (l ++ [:: len])
    end.

Fixpoint build_ctxt (args : p) (input : list (@cst_or_int Z)) : option (list (ident * @cst_or_int Z)) :=
    match args with
    | nil => match input with
        | nil => Some nil
        | _::_ => None
        end
    | var::tl =>
        (val, input') <- build_ctxt_aux (VD_TYP var) input nil;
        ctxt <- build_ctxt tl input';
        Some ((VD_ID var, val)::ctxt)
    end.

Fixpoint eval_node_inner (arch : architecture) (prog : prog_ctxt) (in_names out_names : p)
        (def : def_i) (i : option nat) (input : list cst_or_int)
            : option (list cst_or_int) :=
    match def, i with
    | Single temp_vars eqns, None =>
        args <- build_ctxt in_names input;
        eqns' <- list_of_list_deq nil eqns;
        let tctxt_hd := map proj_types out_names in
        let tctxt_tl := map proj_types (temp_vars ++ in_names) in
        match build_topological_sort (tctxt_hd ++ tctxt_tl) eqns' as opt
        return build_topological_sort (tctxt_hd ++ tctxt_tl) eqns' = opt -> option (list cst_or_int) with
        | None => fun => None
        | Some _ => fun eq =>
            eval_vars arch (tctxt_hd ++ tctxt_tl) args eqns' (map fst tctxt_hd) (termination _ _ _ _ eq)
        end Logic.eq_refl
    | Table l, None => match (in_names, input) with
        | (n1::nil, CoIR d iL _::nil) =>
            match convert_type (VD_TYP n1) with
            | Some (d', len::nil) =>
                if dir_beq d d' && Nat.eqb len (length iL)
                then 
                    size <- match d' with
                        | DirH i | DirV i => Some i
                        | DirB => Some 1 | _ => None end;
                    let iL' := transpose_nat_list size iL in
                    iL2 <- remove_option_from_list (map (fun i => nth_error l (Z.to_nat i)) iL');
                    let output := transpose_nat_list2 iL2 len in
                    Some (CoIR d' output (length output::nil)::nil)
                else None
            | _ => None
            end
        | _ => None
        end
    | Perm l, None => None
    | Multiple l, Some i =>
        eval_node_list arch prog in_names out_names l i input
    | _, _ => None
    end
with eval_node_list arch prog in_names out_names l i input :=
    match l with
    | LDnil => None
    | LDcons hd tl => match i with
        | 0 => eval_node_inner arch prog in_names out_names hd None input
        | S i' => eval_node_list arch prog in_names out_names tl i' input
        end
    end.

Definition eval_node (arch : architecture) (node : def) (prog : prog_ctxt) : node_sem_type :=
    fun opt input =>
        infered <- infer_types (P_IN node) input;
        eval_node_inner arch prog (subst_infer_p infered (P_IN node)) (subst_infer_p infered (P_OUT node)) (subst_infer_def infered (NODE node)) opt input.

Fixpoint eval_prog (arch : architecture) (fprog : prog) : prog_ctxt :=
    match fprog with
    | nil => nil
    | node::prog =>
        let tl := eval_prog arch prog in
        (ID node, eval_node arch node tl)::tl
    end.

Definition prog_sem (arch : architecture) (fprog : prog) : node_sem_type :=
    match eval_prog arch fprog with
    | nil => fun _ _ => None
    | (_, hd)::_ => hd
    end.
        

(* Require Extraction.

Extraction "new_sem" eval_expr list_of_list_deq. *)
