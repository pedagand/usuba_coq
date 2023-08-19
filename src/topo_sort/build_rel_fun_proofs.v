Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST usuba_ASTProp arch
    list_relations termination_funs termination_properties.


Lemma length_update_list {A}:
    forall (f : A -> A) l i,
        length (update_list l i f) = length l.
Proof.
    move=> f l; induction l as [|hd tl HRec]; simpl; [> reflexivity | idtac ].
    move=> [|i]; simpl; auto.
Qed.

Lemma nth_error_update_list {A}:
    forall (f : A -> A) l p1 p2,
        nth_error (update_list l p1 f) p2 =
            if p1 =? p2
            then omap f (nth_error l p2)
            else nth_error l p2.
Proof.
    move=> f l; induction l as [|hd tl]; simpl.
    {
        move=> p1 [|p2]; simpl.
        all: destruct (_ =? _); reflexivity.
    }
    {
        move=> [|p1] [|p2]; simpl; trivial.
    }
Qed.


Lemma length_add_deps:
    forall dtree utree above_uses deps,
        length (add_deps deps dtree utree above_uses) = length deps.
Proof.
    refine (def_tree_find _ _ (fun dtrees =>
        forall utrees above_uses deps, 
            length (add_deps_trees deps dtrees utrees above_uses) = length deps)
        _ _ _ _); simpl.
    {
        intros; rewrite length_update_list; reflexivity.
    }
    {
        move=> dtrees HRec [uses _|uses trees] above_uses deps.
        {
            clear; move: deps; induction extract_defs_l as [|hd tl HRec]; simpl; [> reflexivity | idtac].
            move=> deps; rewrite HRec.
            apply length_update_list.
        }
        {
            apply HRec.
        }
    }
    {
        intros; reflexivity.
    }
    {
        move=> dhd HRec_hd dtl HRec_tl [|uhd utl].
        by intros; reflexivity.
        intros; rewrite HRec_tl; apply HRec_hd.
    }
Qed.

Lemma extract_defs_soundness:
    forall i dtree,
        List.In i (extract_defs dtree) <->
        exists path, dtree_defined dtree path i.
Proof.
    move=> i.
    refine (def_tree_find _ _ (fun dtrees =>
        List.In i (extract_defs_l dtrees) <->
            exists pos path, dtrees_defined dtrees path pos i) _ _ _ _); simpl.
    {
        intros; split.
        by move=> [H|[]]; exists nil; split; trivial.
        by move=> [path [_ H]]; left; assumption.
    }
    {
        move=> dtrees ->.
        split.
        {
            move=> [pos [path H]]; exists (pos :: path); assumption.
        }
        {
            move=> [[|pos path] H]; [> destruct H | do 2 eexists; exact H].
        }
    }
    {
        split.
        by move=> [].
        by move=> [_ [_ []]].
    }
    {
        move=> hd HRec_hd tl HRec_tl.
        rewrite List.in_app_iff; rewrite HRec_hd; rewrite HRec_tl.
        clear; split.
        {
            move=> [[path H]|[pos [path H]]].
            by exists 0; exists path; assumption.
            by exists pos.+1; exists path; assumption.
        }
        {
            move=> [[|pos] [path H]]; [> left | right; exists pos ]; exists path; assumption.
        }
    }
Qed.

Lemma extract_uses_soundness:
    forall i utree,
        List.In i (extract_uses utree) <->
        exists path, utree_used utree path i.
Proof.
    move=> i.
    refine (use_tree_find _ (fun utrees =>
        List.In i (extract_uses_l utrees) <->
            exists pos path, utrees_used utrees path pos i) _ _ _ _); simpl.
    {
        intros; split.
        by intro; exists nil; split; trivial.
        by move=> [path [_ H]]; assumption.
    }
    {
        move=> uses utrees HRec.
        rewrite List.in_app_iff; rewrite HRec; clear HRec.
        split.
        {
            move=> [LIn|[pos [path H]]]; [> exists nil | exists (pos :: path) ].
            all: assumption.
        }
        {
            move=> [[|pos path] H]; [> left; assumption | right; do 2 eexists; exact H ].
        }
    }
    {
        split.
        by move=> [].
        by move=> [_ [_ []]].
    }
    {
        move=> hd HRec_hd tl HRec_tl.
        rewrite List.in_app_iff; rewrite HRec_hd; rewrite HRec_tl.
        clear; split.
        {
            move=> [[path H]|[pos [path H]]].
            by exists 0; exists path; assumption.
            by exists pos.+1; exists path; assumption.
        }
        {
            move=> [[|pos] [path H]]; [> left | right; exists pos ]; exists path; assumption.
        }
    }
Qed.

Lemma test_if_inf_add_deps:
    forall eqns v dtree utree,
        r_dutree eqns v (Some dtree, utree) ->
        forall deps i1 i2 above_uses,
            length deps = length eqns ->
            i1 < length eqns ->
            test_if_inf (add_deps deps dtree utree above_uses) i1 i2 = true <->
                test_if_inf deps i1 i2 = true
                    \/ (exists dpath, dtree_defined dtree dpath i1 /\ List.In i2 above_uses)
                    \/ (exists dpath upath,
                        list_rel_top eq dpath upath /\
                        dtree_defined dtree dpath i1 /\
                        utree_used utree upath i2).
Proof.
    unfold r_dutree; move=> eqns v dtree utree [_ [_ [[typ type_soundness] _]]].
    move: dtree utree type_soundness.
    induction typ as [|d m|typ HRec len].
    {
        move=> dtree utree [dtree_ts utree_ts].
        destruct dtree as [d_pos|]; simpl in dtree_ts; [> idtac | destruct dtree_ts].
        destruct utree as [uses t|]; simpl in utree_ts; destruct utree_ts.
        simpl.
        move=> deps i1 i2 above_uses length_eq; unfold test_if_inf.
        rewrite nth_error_update_list.
        case_eq (d_pos =? i1).
        {
            rewrite Nat.eqb_eq; move=> <-.
            rewrite <-length_eq; move/ltP; rewrite <-nth_error_Some.
            destruct nth_error; simpl.
            2: by move=> H; exfalso; apply H; reflexivity.
            move=> _.
            do 2 rewrite List.existsb_app.
            do 2 rewrite orb_true_iff.
            split; move=> [H|H]; auto.
            {
                right; right.
                do 2 eexists; repeat split.
                by constructor.
                rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                rewrite Nat.eqb_eq in HEq; destruct HEq; assumption.
            }
            {
                destruct H; auto.
                right; left.
                eexists; repeat split.
                rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                rewrite Nat.eqb_eq in HEq; destruct HEq; assumption.
            }
            {
                destruct H as [[dpath [_ LIn]]|[dpath [upath [_ [_ [_ LIn]]]]]].
                {
                    right; left; rewrite List.existsb_exists.
                    eexists; rewrite Nat.eqb_eq; split; [> exact LIn | reflexivity ].
                }
                {
                    left; rewrite List.existsb_exists.
                    eexists; rewrite Nat.eqb_eq; split; [> exact LIn | reflexivity ].
                }
            }
        }
        {
            rewrite <-not_true_iff_false; rewrite Nat.eqb_eq.
            move=> NEq.
            rewrite <-length_eq; move/ltP; rewrite <-nth_error_Some.
            destruct nth_error; simpl.
            2: by move=> H; exfalso; apply H; reflexivity.
            move=> _; split; auto.
            move=> [H|[[dpath [[_ Abs] _]]|[dpath [upath [_ [[_ Abs] _]]]]]]; [> assumption | exfalso | exfalso ].
            all: exact (NEq Abs).
        }
    }
    {
        move=> dtree utree [dtree_ts utree_ts].
        destruct dtree as [d_pos|]; simpl in dtree_ts; [> idtac | destruct dtree_ts].
        destruct utree as [uses t|]; simpl in utree_ts; destruct utree_ts.
        simpl.
        move=> deps i1 i2 above_uses length_eq; unfold test_if_inf.
        rewrite nth_error_update_list.
        case_eq (d_pos =? i1).
        {
            rewrite Nat.eqb_eq; move=> <-.
            rewrite <-length_eq; move/ltP; rewrite <-nth_error_Some.
            destruct nth_error; simpl.
            2: by move=> H; exfalso; apply H; reflexivity.
            move=> _.
            do 2 rewrite List.existsb_app.
            do 2 rewrite orb_true_iff.
            split; move=> [H|H]; auto.
            {
                right; right.
                do 2 eexists; repeat split.
                by constructor.
                rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                rewrite Nat.eqb_eq in HEq; destruct HEq; assumption.
            }
            {
                destruct H; auto.
                right; left.
                eexists; repeat split.
                rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                rewrite Nat.eqb_eq in HEq; destruct HEq; assumption.
            }
            {
                destruct H as [[dpath [_ LIn]]|[dpath [upath [_ [_ [_ LIn]]]]]].
                {
                    right; left; rewrite List.existsb_exists.
                    eexists; rewrite Nat.eqb_eq; split; [> exact LIn | reflexivity ].
                }
                {
                    left; rewrite List.existsb_exists.
                    eexists; rewrite Nat.eqb_eq; split; [> exact LIn | reflexivity ].
                }
            }
        }
        {
            rewrite <-not_true_iff_false; rewrite Nat.eqb_eq.
            move=> NEq.
            rewrite <-length_eq; move/ltP; rewrite <-nth_error_Some.
            destruct nth_error; simpl.
            2: by move=> H; exfalso; apply H; reflexivity.
            move=> _; split; auto.
            move=> [H|[[dpath [[_ Abs] _]]|[dpath [upath [_ [[_ Abs] _]]]]]]; [> assumption | exfalso | exfalso ].
            all: exact (NEq Abs).
        }
    }
    {
        move=> [d_pos|dtrees] [uses utyp|uses utrees] [def_ts used_ts]; simpl in *.
        {
            destruct used_ts; clear def_ts.
            move=> deps i1 i2 above_uses length_eq; unfold test_if_inf.
            rewrite nth_error_update_list.
            case_eq (d_pos =? i1).
            {
                rewrite Nat.eqb_eq; move=> <-.
                rewrite <-length_eq; move/ltP; rewrite <-nth_error_Some.
                destruct nth_error; simpl.
                2: by move=> H; exfalso; apply H; reflexivity.
                move=> _.
                do 2 rewrite List.existsb_app.
                do 2 rewrite orb_true_iff.
                split; move=> [H|H]; auto.
                {
                    right; right.
                    do 2 eexists; repeat split.
                    by constructor.
                    rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                    rewrite Nat.eqb_eq in HEq; destruct HEq; assumption.
                }
                {
                    destruct H; auto.
                    right; left.
                    eexists; repeat split.
                    rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                    rewrite Nat.eqb_eq in HEq; destruct HEq; assumption.
                }
                {
                    destruct H as [[dpath [_ LIn]]|[dpath [upath [_ [_ [_ LIn]]]]]].
                    {
                        right; left; rewrite List.existsb_exists.
                        eexists; rewrite Nat.eqb_eq; split; [> exact LIn | reflexivity ].
                    }
                    {
                        left; rewrite List.existsb_exists.
                        eexists; rewrite Nat.eqb_eq; split; [> exact LIn | reflexivity ].
                    }
                }
            }
            {
                rewrite <-not_true_iff_false; rewrite Nat.eqb_eq.
                move=> NEq.
                rewrite <-length_eq; move/ltP; rewrite <-nth_error_Some.
                destruct nth_error; simpl.
                2: by move=> H; exfalso; apply H; reflexivity.
                move=> _; split; auto.
                move=> [H|[[dpath [[_ Abs] _]]|[dpath [upath [_ [[_ Abs] _]]]]]]; [> assumption | exfalso | exfalso ].
                all: exact (NEq Abs).
            }
        }
        {
            move=> deps i1 i2 above_uses length_eq.
            unfold test_if_inf; rewrite nth_error_update_list.
            case_eq (d_pos =? i1); [> idtac | rewrite <-not_true_iff_false ]; rewrite Nat.eqb_eq.
            {
                move=> <-; rewrite <-length_eq; move/ltP; rewrite <-nth_error_Some.
                destruct nth_error; simpl.
                2: by move=> H; exfalso; apply H; reflexivity.
                move=> _; do 3 rewrite List.existsb_app; do 3 rewrite orb_true_iff.
                rewrite or_assoc; split; move=> [H|[H|H]].
                {
                    right; right; do 2 exists nil.
                    split; [> constructor | idtac ].
                    split; [> split; reflexivity | idtac ].
                    rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                    rewrite Nat.eqb_eq in HEq; destruct HEq.
                    assumption.
                }
                {
                    right; right.
                    rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                    rewrite Nat.eqb_eq in HEq; destruct HEq.
                    pose (p := extract_uses_soundness i2 (UTRec nil utrees)); simpl in p.
                    rewrite p in LIn; clear p.
                    destruct LIn as [[|path_hd path_tl] H].
                    by destruct H.
                    exists nil; exists (path_hd :: path_tl).
                    split; [> by constructor | idtac ].
                    split; [> split; reflexivity | idtac ].
                    assumption.
                }
                {
                    destruct H as [H|H]; auto.
                    right; left.
                    exists nil; split; [> split; reflexivity | idtac ].
                    rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                    rewrite Nat.eqb_eq in HEq; destruct HEq; assumption.
                }
                {
                    auto.
                }
                {
                    destruct H as [dpath [_ LIn]].
                    right; right; left.
                    rewrite List.existsb_exists; eexists.
                    rewrite Nat.eqb_eq.
                    split; [> exact LIn | reflexivity ].
                }
                {
                    destruct H as [dpath [[|upath_hd upath_tl] [_ [_ H]]]].
                    {
                        left; rewrite List.existsb_exists; eexists.
                        rewrite Nat.eqb_eq.
                        split; [> exact H | reflexivity ].
                    }
                    {
                        right; left.
                        rewrite List.existsb_exists.
                        eexists; rewrite Nat.eqb_eq; split; [> idtac | reflexivity ].
                        pose (p := extract_uses_soundness i2 (UTRec nil utrees)); simpl in p.
                        rewrite p; clear p.
                        exists (upath_hd :: upath_tl); auto.
                    }
                }
            }
            {
                move=> NEq; rewrite <-length_eq; move/ltP; rewrite <-nth_error_Some.
                destruct nth_error; simpl.
                2: by move=> H; exfalso; apply H; reflexivity.
                move=> _.
                split; auto.
                move=> [H|[[dpath [[_ Abs] _]]|[dpath [upath [_ [[_ Abs] _]]]]]]; [> assumption | exfalso | exfalso ].
                all: exact (NEq Abs).
            }
        }
        {
            move=> deps i1 i2 above_uses length_eq HInf.
            assert (forall l deps, List.existsb (Nat.eqb i1) l = false ->
                test_if_inf (fold_left
                    (fun deps0 : seq (seq nat) =>
                        (update_list deps0)^~ (fun l : seq nat => uses ++ above_uses ++ l))
                    l deps) i1 i2 = true <->
                        test_if_inf deps i1 i2 = true) as NotInTail.
            {
                clear; move=> l.
                induction l as [|hd tl HRec]; simpl.
                by split; trivial.
                move=> deps; rewrite orb_false_iff.
                move=> [NEq Nexist]; rewrite HRec; trivial.
                unfold test_if_inf.
                rewrite nth_error_update_list.
                rewrite Nat.eqb_sym; rewrite NEq.
                split; trivial.
            }
            case_eq (List.existsb (Nat.eqb i1) (extract_defs_l dtrees)).
            all: move=> Lexistsb.
            {
                assert (test_if_inf (fold_left
                    (fun deps0 : seq (seq nat) =>
                        (update_list deps0)^~ (fun l : seq nat => uses ++ above_uses ++ l))
                    (extract_defs_l dtrees) deps) i1 i2 = true <->
                        List.In i2 uses \/ List.In i2 above_uses \/ test_if_inf deps i1 i2 = true) as ->.
                {
                    move: NotInTail HInf Lexistsb; rewrite <-length_eq.
                    clear; move=> NotInTail; move: deps.
                    induction extract_defs_l as [|hd tl HRec]; simpl.
                    by split; trivial.
                    move=> deps HInf.
                    case_eq (List.existsb (Nat.eqb i1) tl).
                    {
                        move=> Lexistb _; rewrite HRec; trivial.
                        2: by rewrite length_update_list; assumption.
                        split; move=> [H|[H|H]]; auto; move: H.
                        all: unfold test_if_inf; rewrite nth_error_update_list; destruct (_ =? _).
                        all: destruct nth_error; simpl.
                        2,4,6,8: move=> H; discriminate H.
                        {
                            do 2 rewrite List.existsb_app; do 2 rewrite orb_true_iff.
                            move=> [H|[H|H]]; auto.
                            all: rewrite List.existsb_exists in H; destruct H as [x [LIn HEq]].
                            all: rewrite Nat.eqb_eq in HEq; destruct HEq; auto.
                        }
                        {
                            auto.
                        }
                        {
                            move=> H; right; right.
                            do 2 rewrite List.existsb_app; do 2 rewrite orb_true_iff; auto.
                        }
                        {
                            auto.
                        }
                    }
                    rewrite orb_false_r.
                    move=> Nexist HEq; rewrite NotInTail; trivial.
                    unfold test_if_inf.
                    rewrite nth_error_update_list.
                    rewrite Nat.eqb_sym; rewrite HEq.
                    move: HInf; move/ltP.
                    rewrite <-nth_error_Some.
                    destruct nth_error.
                    2: by move=> H; exfalso; apply H; reflexivity.
                    move=> _; simpl.
                    do 2 rewrite List.existsb_app; do 2 rewrite orb_true_iff.
                    split.
                    {
                        move=> [H|[H|H]]; auto.
                        all: rewrite List.existsb_exists in H; destruct H as [x [LIn H]].
                        all: rewrite Nat.eqb_eq in H; destruct H; auto.
                    }
                    {
                        move=> [H|[H|H]]; auto; [> left | right; left ].
                        all: rewrite List.existsb_exists; exists i2; split; trivial.
                        all: exact (Nat.eqb_refl _).
                    }
                }
                {
                    split.
                    {
                        move=> [H|[H|H]]; auto.
                        all: right; [> right | left ].
                        all: move: H Lexistsb; clear; move=> H Lexistsb.
                        all: rewrite List.existsb_exists in Lexistsb.
                        all: destruct Lexistsb as [x [LIn HEq]].
                        all: rewrite Nat.eqb_eq in HEq; destruct HEq.
                        all: pose (p := extract_defs_soundness i1 (DTRec _ dtrees)); simpl in p.
                        all: rewrite p in LIn; clear p.
                        all: destruct LIn as [dpath dH]; exists dpath.
                        by exists nil; split; [> constructor | auto ].
                        by split; assumption.
                    }
                    {
                        move=> [H|[[dpath [_ H]]|[dpath [upath [_ [_ [_ H]]]]]]]; auto.
                    }
                }
            }
            {
                rewrite NotInTail; trivial.
                split; auto.
                move=> [H|[H|H]]; trivial.
                all: exfalso; rewrite <-not_true_iff_false in Lexistsb; apply Lexistsb.
                {
                    destruct H as [[|dpos dpath] [H _]].
                    by destruct H.
                    rewrite List.existsb_exists; exists i1.
                    split; [> idtac | exact (Nat.eqb_refl _)].
                    pose (p := extract_defs_soundness i1 (DTRec _ dtrees)); simpl in p; rewrite p.
                    exists (dpos :: dpath); assumption.
                }
                {
                    destruct H as [[|dpos dpath] [upath [lrel [H [upath_empty LIn]]]]].
                    by destruct H.
                    rewrite List.existsb_exists; exists i1.
                    split; [> idtac | exact (Nat.eqb_refl _)].
                    pose (p := extract_defs_soundness i1 (DTRec _ dtrees)); simpl in p; rewrite p.
                    exists (dpos :: dpath); assumption.
                }
            }
        }
        {
            move=> deps i1 i2 above_uses length_eq HInf.
            move: deps length_eq dtrees utrees def_ts used_ts.
            induction len as [|len HRec_len].
            all: move=> deps length_eq [|dhd dtl] [|uhd utl]; simpl.
            {
                move=> _ _; split; auto.
                move=> [H|[[[|phd ptl] [[] _]]| [[|phd ptl] [upath [_ [[] _]]]]]].
                assumption.
            }
            by move=> _ [_ []].
            by move=> [_ []].
            by move=> [_ []].
            by move=> H; discriminate H.
            by move=> H; discriminate H.
            by move=> _ H; discriminate H.
            move=> [dhd_ts dtl_ts] [uhd_ts utl_ts].
            rewrite HRec_len; trivial.
            2: by rewrite length_add_deps; assumption.
            rewrite HRec; auto.
            clear; split.
            {
                move=> [[eq_true|[above_hd|rec_hd]]|[above_tl|rec_tl]].
                by left; assumption.
                {
                    right; destruct above_hd as [path [dt_defined LIn]].
                    rewrite List.in_app_iff in LIn.
                    destruct LIn as [LIn|LIn]; [> right | left]; exists (0 :: path).
                    by exists nil; split; [> constructor | split; assumption ].
                    by split; assumption.
                }
                {
                    right; right.
                    destruct rec_hd as [dpath [upath [lrel [dt_defined ut_used]]]].
                    exists (0 :: dpath); exists (0 :: upath).
                    split; [> constructor | split ]; trivial.
                }
                {
                    right; left.
                    destruct above_tl as [[|pos path] [H LIn]]; [> destruct H | idtac ].
                    exists (pos.+1 :: path); split; assumption.
                }
                {
                    right; right.
                    destruct rec_tl as [[|dpos dpath] [[|upos upath] [lrel [dH uH]]]].
                    1,2: by destruct dH.
                    by exists (dpos.+1 :: dpath); exists nil; split; [> constructor | auto ].
                    exists (dpos.+1 :: dpath); exists (upos.+1 :: upath).
                    inversion lrel.
                    split; [> constructor; [> f_equal | idtac ] | split ]; assumption.
                }
            }
            {
                move=> [H|[[[|[|pos] path] [H LIn]]|[[|[|dpos] dpath] H]]].
                by do 2 left; assumption.
                by destruct H.
                {
                    left; right; left.
                    eexists; split; [> exact H | idtac ].
                    rewrite List.in_app_iff; right; assumption.
                }
                {
                    right; left.
                    exists (pos :: path); split; assumption.
                }
                by destruct H as [upath [_ [[] _]]].
                all: destruct H as [[|[|upos] upath] [lrel [dH uH]]].
                {
                    left; right; left.
                    eexists; split; [> exact dH | idtac ].
                    rewrite List.in_app_iff; left; assumption.
                }
                {
                    left; right; right.
                    eexists; eexists; split; [> idtac | split; [> exact dH | exact uH ]].
                    inversion lrel; assumption.
                }
                by inversion lrel; discriminate.
                {
                    right; right.
                    exists (dpos :: dpath); exists nil; split.
                    by constructor.
                    split; assumption.
                }
                by inversion lrel; discriminate.
                {
                    right; right.
                    exists (dpos :: dpath); exists (upos :: upath); split.
                    by inversion lrel as [| |h1 h2 t1 t2 H]; inversion H; constructor; trivial.
                    split; assumption.
                }
            }
        }
    }
Qed.

Lemma nth_error_genlist {A}:
    forall (el : A) len i,
        nth_error (gen_list el len) i = None \/
        nth_error (gen_list el len) i = Some el.
Proof.
    move=> el; induction len as [|len HRec]; simpl; move=> [|i]; simpl; auto.
Qed.
