Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST usuba_ASTProp arch semantic_base coq_missing_lemmas list_relations.

Fixpoint get_ident (v : var) :=
    match v with
    | Var v => v
    | Index v _ => get_ident v
    end.

Lemma leq_Cases:
    forall l1 l2,
        l1 <= l2 -> l1 = l2 \/ l1 < l2.
Proof.
    move=> l1; induction l1 as [|l1 HRec].
    all: move=> [|l2]; simpl; auto.
    rewrite ltnS.
    move=> H; destruct (HRec _ H) as [->| H']; auto.
Qed.

(* Vars of expressions *)

Fixpoint expr_freefullvars (e : expr) : Ensemble var :=
    match e with
    | Const _ _ => Empty_set _
    | ExpVar v | Shuffle v _ => Singleton _ v
    | Tuple el | BuildArray el => exprl_freefullvars el
    | Not e | Shift _ e _ | Bitmask e _ => expr_freefullvars e
    | Log _ e1 e2 | Arith _ e1 e2 => Union _ (expr_freefullvars e1) (expr_freefullvars e2)
    | Pack e1 e2 _ => Union _ (expr_freefullvars e1) (expr_freefullvars e2)
    | Fun _ exprl | Fun_v _ _ exprl => exprl_freefullvars exprl
    end
with exprl_freefullvars el :=
    match el with
    | Enil => Empty_set _
    | ECons e el => Union _ (expr_freefullvars e) (exprl_freefullvars el)
    end.
    
Fixpoint aexpr_freevars (e : arith_expr) : Ensemble ident :=
    match e with
    | Var_e i => Singleton ident i
    | Const_e _ => Empty_set ident
    | Op_e _ e1 e2 => Union ident (aexpr_freevars e1) (aexpr_freevars e2)
    end.

Fixpoint aexprl_freevars (e : list arith_expr) : Ensemble ident :=
    match e with
    | nil => Empty_set ident
    | h :: tl => Union ident (aexpr_freevars h) (aexprl_freevars tl)
    end.

Definition indexing_freevars  (v : indexing) : Ensemble ident :=
    match v with
    | IInd ae => aexpr_freevars ae
    | IRange ae1 ae2 => Union ident (aexpr_freevars ae1) (aexpr_freevars ae2)
    | ISlice aeL => aexprl_freevars aeL
    end.

Fixpoint indexingl_freevars (v : seq indexing) : Ensemble ident :=
    match v with
    | nil => Empty_set ident
    | hd::tl => Union _ (indexing_freevars hd) (indexingl_freevars tl)
    end.

Fixpoint var_freevars (v : var) : Ensemble ident :=
    match v with
    | Var var => Singleton ident var
    | Index v i => Union ident (var_freevars v) (indexingl_freevars i)
    end.

Fixpoint varl_freevars vl :=
    match vl with
    | nil => Empty_set ident
    | v :: tl => Union ident (var_freevars v) (varl_freevars tl)
    end.

Fixpoint expr_freevars (e : expr) : Ensemble ident :=
    match e with
    | Const _ _ => Empty_set ident
    | ExpVar v => var_freevars v
    | Tuple el | BuildArray el => exprl_freevars el
    | Not e => expr_freevars e
    | Log _ e1 e2 | Arith _ e1 e2 => Union ident (expr_freevars e1) (expr_freevars e2)
    | Shift _ expr aexpr => Union ident (expr_freevars expr) (aexpr_freevars aexpr)
    | Shuffle v _ => var_freevars v
    | Bitmask expr aexpr => Union ident (expr_freevars expr) (aexpr_freevars aexpr)
    | Pack e1 e2 _ => Union ident (expr_freevars e1) (expr_freevars e2)
    | Fun f exprl => Union ident (Singleton ident f) (exprl_freevars exprl)
    | Fun_v f aexpr exprl => Union ident (Singleton ident f) (Union ident (aexpr_freevars aexpr) (exprl_freevars exprl))
    end
with exprl_freevars el :=
    match el with
    | Enil => Empty_set ident
    | ECons e el => Union ident (expr_freevars e) (exprl_freevars el)
    end.

Fixpoint deq_vars (d : deq) : Ensemble ident :=
    match d with 
    | Eqn v e _ => Union ident (expr_freevars e) (varl_freevars v)
    | Loop i ae1 ae2 eqns _ =>
        Union ident (Singleton ident i)
            (Union ident (aexpr_freevars ae1)
                (Union ident (aexpr_freevars ae2) (deqs_vars eqns)))
    end
with deqs_vars (d : list_deq) : Ensemble ident :=
    match d with
    | Dnil => Empty_set ident
    | Dcons hd tl => Union ident (deq_vars hd) (deqs_vars tl)
    end.

Fixpoint deq_boundvars (d : deq) : Ensemble ident :=
    match d with 
    | Eqn v e _ => (varl_freevars v)
    | Loop i _ _ eqns _ => Union ident (Singleton ident i) (deqs_boundvars eqns)
    end
with deqs_boundvars (d : list_deq) : Ensemble ident :=
    match d with
    | Dnil => Empty_set ident
    | Dcons hd tl => Union ident (deq_boundvars hd) (deqs_boundvars tl)
    end.
    

(* Properties on gen_range *)

Lemma gen_range_in_l:
    forall n1 n2,
        List.In n1 (gen_range n1 n2).
Proof.
    move=> n1 n2; unfold gen_range.
    case_eq (n1 <=? n2).
    {
        rewrite Nat.leb_le; move/leP.
        induction n2 as [|n2 HRec]; simpl.
        {
            destruct n1; auto.
        }
        {
            move=> H; destruct (leq_Cases _ _ H) as [->|HInf].
            {
                case_eq (n2.+1 <? n2.+1); simpl; auto.
                clear; move=> Abs; exfalso.
                apply (Nat.nle_succ_diag_l n2.+1).
                apply/leP.
                rewrite Nat.ltb_lt in Abs; move/ltP in Abs.
                assumption.
            }
            {
                move/ltP in HInf.
                rewrite <-Nat.ltb_lt in HInf; rewrite HInf.
                rewrite List.in_app_iff; left; apply HRec.
                rewrite Nat.ltb_lt in HInf; move/ltP in HInf; trivial.
            }
        }
    }
    {
        destruct n1; simpl.
        by move=> H; inversion H.
        destruct n2.
        {
            case_eq (n1.+1 <? 0).
            {
                rewrite Nat.ltb_lt.
                move=> H; exfalso.
                exact (Nat.nlt_0_r _ H).
            }
            {
                intros; simpl; left; reflexivity.
            }
        }
        {
            case_eq (n1.+1 <? n2.+1).
            {
                rewrite Nat.ltb_lt; move=> H.
                apply Nat.lt_le_pred in H; simpl in H.
                move/leP in H; apply ltnW in H.
                move/leP in H; rewrite <-Nat.leb_le in H; rewrite H.
                move=> H'; inversion H'.
            }
            {
                intros; simpl.
                left; reflexivity.
            }
        }
    }
Qed.

Lemma gen_range_in_r:
    forall n1 n2,
        List.In n2 (gen_range n1 n2).
Proof.
    move=> n1 n2; unfold gen_range.
    case_eq (n1 <=? n2).
    {
        rewrite Nat.leb_le; move/leP.
        destruct n2; simpl.
        {
            intro; left; reflexivity.
        }
        {
            destruct (_ <? _); simpl; intro.
            {
                rewrite List.in_app_iff; right; simpl; left; reflexivity.
            }
            {
                left; reflexivity.
            }
        }
    }
    {
        move=> H.
        assert (n2 <= n1) as H'.
        {
            apply/leP; rewrite <-Nat.nlt_ge.
            move=> H'; move/ltP in H'.
            apply ltnW in H'.
            rewrite <-not_true_iff_false in H; apply H.
            rewrite Nat.leb_le; apply/leP.
            assumption.
        }
        clear H; induction n1 as [|n1 HRec].
        all: unfold gen_range_decr; fold gen_range_decr.
        {
            destruct n2; simpl in *.
            by left; reflexivity.
            inversion H'.
        }
        {
            case_eq (n1.+1 <? n2); simpl.
            {
                rewrite Nat.ltb_lt; rewrite <-Nat.nle_gt.
                move=> H; apply H.
                apply/leP; assumption.
            }
            {
                destruct (leq_Cases _ _ H') as [->|HInf].
                by intro; left; reflexivity.
                intro; right; apply HRec.
                apply/leP; apply le_S_n; apply/leP; assumption.
            }
        }
    }
Qed.

Lemma gen_range_decr_comp:
    forall i1 i2,
        gen_range_decr i1 i2 =
            if i1 <? i2
            then nil
            else
                i1::match i1 with
                | 0 => nil
                | i1'.+1 => gen_range_decr i1' i2
                end.
Proof.
    move=> i1; destruct i1; simpl; reflexivity.
Qed.

Lemma gen_range_completeness:
    forall i1 i2,
        forall i, List.In i (gen_range i1 i2) <->
            (i1 <= i /\ i <= i2) \/ (i2 <= i /\ i <= i1).
Proof.
    move=> i1 i2; unfold gen_range.
    case_eq (i1 <=? i2).
    2: rewrite <-not_true_iff_false.
    all: rewrite Nat.leb_le.
    {
        move/leP; move=> HInf.
        assert (forall i, List.In i (gen_range_incr i1 i2) <-> i1 <= i /\ i <= i2) as H.
        {
            induction i2 as [|i2 HRec]; simpl.
            {
                move=> i; split.
                by move=> [<-|[]].
                destruct i.
                by intro; left; reflexivity.
                by move=> [_ Abs]; auto.
            }
            case_eq (i1 <? i2.+1); [> idtac | rewrite <-not_true_iff_false ].
            {
                rewrite Nat.ltb_lt; move/ltP; rewrite ltnS.
                move=> H i; rewrite List.in_app_iff; simpl.
                split; auto.
                {
                    rewrite HRec; trivial.
                    move=> [[Ineq1 Ineq2]|[<-|[]]]; auto.
                }
                {
                    move=> [Ineq1 Ineq2].
                    destruct (leq_Cases _ _ Ineq2) as [->|Ineq2'].
                    by right; left; reflexivity.
                    by left; rewrite HRec; auto.
                }
            }
            {
                rewrite Nat.ltb_lt; move=> NotLt; simpl.
                destruct (leq_Cases _ _ HInf) as [->|SInf].
                all: move=> i; split.
                1,3: move=> [<-|[]]; auto.
                {
                    move=> [SInf1 SInf2]; left.
                    move/leP in SInf1; move/leP in SInf2.
                    exact (Nat.le_antisymm _ _ SInf1 SInf2).
                }
                {
                    move/ltP in SInf.
                    destruct (NotLt SInf).
                }
            }
        }
        {
            move=> i; rewrite H; clear H; split.
            by move=> [H1 H2]; auto.
            move=> [[H1 H2]|[H1 H2]]; auto.
            move/leP in HInf; move/leP in H1; move/leP in H2.
            destruct (Nat.le_antisymm _ _ HInf (Nat.le_trans _ _ _ H1 H2)).
            split; apply/leP; assumption.
        }
    }
    {
        rewrite Nat.nle_gt; move/ltP; move=> HSup.
        assert (forall i, List.In i (gen_range_decr i1 i2) <-> i2 <= i /\ i <= i1) as H.
        {
            induction i1 as [|i1 HRec]; simpl.
            by idtac.
            case_eq (i1.+1 <? i2); [> idtac | rewrite <-not_true_iff_false ].
            {
                rewrite Nat.ltb_lt; rewrite <-Nat.nle_gt; move=> Abs; exfalso.
                apply Abs; apply/leP.
                apply ltnW; assumption.
            }
            rewrite Nat.ltb_lt; move/ltP; move/negP.
            move=> H i; simpl.
            case_eq (i1 <? i2).
            {
                rewrite gen_range_decr_comp; move=> SInf; rewrite SInf; split; simpl.
                by move=> [<-|[]]; split; auto.
                rewrite Nat.ltb_lt in SInf; move/ltP in SInf.
                destruct (leq_Cases _ _ SInf) as [->|SInf2].
                2: by destruct (H SInf2).
                move=> [Inf1 Inf2]; left.
                apply Nat.le_antisymm; apply/leP; assumption.
            }
            rewrite <-not_true_iff_false; rewrite Nat.ltb_lt.
            rewrite Nat.nlt_ge; move/leP.
            move=> HInf; destruct (leq_Cases _ _ HInf) as [HEq|HInf'].
            {
                destruct HEq; destruct i2; simpl.
                {
                    split.
                    by move=> [<-|[<-|[]]]; auto.
                    destruct i as [|[]]; auto.
                    move=> [_ Abs]; exfalso.
                    inversion Abs.
                }
                rewrite Nat.ltb_irrefl.
                rewrite gen_range_decr_comp.
                move: (Nat.lt_succ_diag_r i2); rewrite <-Nat.ltb_lt.
                move=> ->; split; simpl.
                by move=> [<-|[<-|[]]]; auto.
                move=> [InfB HInf'].
                destruct (leq_Cases _ _ HInf') as [|SInf]; [> left; symmetry; assumption | right].
                destruct (leq_Cases _ _ SInf) as [Eq|SInf'].
                by inversion Eq; left; reflexivity.
                simpl in SInf.
                left; apply Nat.le_antisymm; apply/leP; auto.
            }
            {
                move: (HRec HInf'); move=> ->.
                split.
                {
                    move=> [<-|[H1 H2]]; auto.
                }
                {
                    move=> [H1 H2].
                    destruct (leq_Cases _ _ H2); auto.
                }
            }
        }
        {
            move=> i; rewrite H; clear H; split.
            by move=> H; right; assumption.
            move=> [[H1 H2]|H]; trivial.
            move/ltP in HSup; rewrite <-Nat.nle_gt in HSup.
            exfalso; apply HSup.
            apply (Nat.le_trans _ i); apply/leP; assumption.
        }
    }
Qed.

Lemma gen_range_soundness:
    forall i1 i2,
        Forall (fun i => (i1 <= i /\ i <= i2) \/ (i2 <= i /\ i <= i1)) (gen_range i1 i2).
Proof.
    move=> i1 i2; rewrite Forall_forall; move=> i.
    rewrite <-gen_range_completeness; trivial.
Qed.

(* Properties on prod_list *)

Fixpoint simpl_form (form : list nat) : list nat :=
    match form with
    | nil => nil
    | 1::tl => simpl_form tl
    | hd::tl => hd::simpl_form tl
    end.

Lemma simpl_form_preserve_prod:
    forall form, prod_list form = prod_list (simpl_form form).
Proof.
    move=> form; induction form as [|[|[|hd'']] tl HRec]; simpl; trivial.
    + rewrite <- HRec; clear HRec.
        unfold muln, muln_rec; rewrite Nat.mul_1_l; reflexivity.
    + rewrite <- HRec; reflexivity.
Qed.

Lemma prod_list_append:
    forall l1 l2,
        prod_list (l1 ++ l2)%list = prod_list l1 * prod_list l2.
Proof.
    move=> l1; induction l1 as [|hd l1 HRec]; simpl; move=> l2.
    {
        unfold muln, muln_rec; rewrite Nat.mul_1_l; reflexivity.
    }
    {
        rewrite HRec.
        unfold muln, muln_rec; rewrite Nat.mul_assoc; reflexivity.
    }
Qed.

(* Properties on find_val *)

Inductive distinct : list (ident) -> Prop :=
    | is_map_Nil : distinct nil
    | is_map_cons : forall id tl,
        Forall (fun id' => id <> id') tl ->
        distinct tl -> distinct (id::tl).

Lemma is_map_soundness {A}:
    forall v t tctxt,
        List.In (v, t) tctxt ->
        distinct [seq i.1 | i <- tctxt] ->
        @find_val A tctxt v = Some t.
Proof.
    move=> v t tctxt; induction tctxt as [|[v' t'] tl HRec]; simpl.
    by move=> [].
    move=> [H|LIn] is_map.
    {
        inversion H; rewrite ident_beq_refl; reflexivity.
    }
    {
        inversion is_map as [|hd' tl' HForall is_map_tl H0].
        case_eq (ident_beq v v'); auto.
        rewrite ident_beq_eq; move=> HEq; destruct HEq.
        rewrite Forall_forall in HForall.
        exfalso; apply (HForall v); trivial.
        apply (in_map (fun i => i.1)) in LIn; simpl in LIn.
        auto.
    }
Qed.

Lemma find_val_In {V} :
    forall ctxt k v,
        @find_val V ctxt k = Some v -> List.In (k, v) ctxt.
Proof.
    move=> ctxt k v; induction ctxt as [|[k' v'] tl HRec]; simpl.
    by idtac.
    case_eq (ident_beq k k'); auto.
    rewrite ident_beq_eq; move=> -> H; inversion H; auto.
Qed.

(* Relation between find_val and find_const *)

Lemma find_val_imp_find_const:
    forall x ctxt1 ctxt2,
        find_val ctxt1 x = find_val ctxt2 x -> find_const ctxt1 x = find_const ctxt2 x.
Proof.
    move=> x ctxt1.
    induction ctxt1 as [|[n1 v1] ctxt1 HRec1]; simpl.
    {
        move=> ctxt2; induction ctxt2 as [|[n v] tl HRec]; simpl; trivial.
        case (ident_beq x n).
        + discriminate.
        + assumption.
    }
    {
        move=> ctxt2.
        case (ident_beq x n1); auto.
        induction ctxt2 as [|[n2 v2] ctxt2 HRec2]; simpl.
        + discriminate.
        + case (ident_beq x n2).
            - move=> HEq; inversion HEq; reflexivity.
            - assumption.
    }
Qed.

(* linearize_list_value properties *)

Lemma map_CoIL_is_lin {A : Type}:
    forall l, @linearize_list_value A [seq CoIL i | i <- l] nil = [seq CoIL i | i <- l].
Proof.
    move=> l; induction l as [|hd tl HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Theorem linearize_map_CoIL {A : Type} :
    forall l1 l2, @linearize_list_value A (List.map CoIL l1) l2 = (List.map CoIL l1) ++ l2.
Proof.
    move=> l1 l2; induction l1 as [|hd l1 HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

(* take n property *)

Lemma take_n_sum {A : Type} :
    forall l l2: list A, forall n, length l = n -> take_n n (l ++ l2) = Some (l, l2).
Proof.
    move=> l l2; induction l as [|hd tl HRec]; simpl.
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

Lemma take_n_all {A : Type} :
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

Lemma take_n_soundness2 { A : Type} :
    forall i l,
        i <= length l ->
        exists l1 l2, @take_n (option A) i (List.map Some l) = Some (List.map Some l1, map Some l2) /\ l = l1 ++ l2 /\ length l1 = i.
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

Lemma try_take_n_all { A : Type} :
    forall i l,
        i = length l ->
        @try_take_n A i l = (l, SumR nil).
Proof.
    move=> i; induction i as [|i HRec]; simpl.
    {
        move=> []; simpl; trivial.
        by discriminate.
    }
    {
        move=> [|hd tl]; simpl.
        by discriminate.
        specialize HRec with tl.
        move=> HEq; move: HRec.
        impl_tac.
        + inversion HEq; reflexivity.
        + move=> ->; reflexivity.
    }
Qed.

Lemma try_take_n_soundness { A : Type} :
    forall i l1 l2,
        i = length l1 ->
        @try_take_n A i (l1 ++ l2) = (l1, SumR l2).
Proof.
    move=> i l1 l2; move: l1; induction i as [|i HRec]; simpl.
    {
        move=> []; simpl; trivial.
        by discriminate.
    }
    {
        move=> [|hd tl]; simpl.
        by discriminate.
        specialize HRec with tl.
        move=> HEq; move: HRec.
        impl_tac.
        + inversion HEq; reflexivity.
        + move=> ->; reflexivity.
    }
Qed.

(* Subexpr *)

Fixpoint is_subexpr (e' e : expr) : Prop :=
    e' = e \/
    match e with
    | Const _ _ | ExpVar _ => False
    | Shuffle v _ => ExpVar v = e'
    | Fun _ el | Fun_v _ _ el | Tuple el | BuildArray el => is_subexpr_l e' el
    | Not e | Shift _ e _ | Bitmask e _ => is_subexpr e' e
    | Log _ e1 e2 | Arith _ e1 e2 | Pack e1 e2 _ => is_subexpr e' e1 \/ is_subexpr e' e2
    end
with is_subexpr_l e' el :=
    match el with
    | Enil => False
    | ECons hd tl => is_subexpr e' hd \/ is_subexpr_l e' tl
    end.

Lemma is_subexpr_refl:
    forall e, is_subexpr e e.
Proof.
    move=> e; destruct e; simpl; auto.
Qed.

Lemma is_subexpr_trans:
    forall e1 e2 e3,
        is_subexpr e1 e2 ->
        is_subexpr e2 e3 ->
        is_subexpr e1 e3.
Proof.
    move=> e1 e2 e3; move: e3.
    refine (expr_find _ (fun eL => is_subexpr e1 e2 -> is_subexpr_l e2 eL -> is_subexpr_l e1 eL) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); simpl.
    {
        move=> z o is_sub [HEq|[]].
        rewrite HEq in is_sub.
        simpl in is_sub; trivial.
    }
    {
        move=> v is_sub [HEq|[]].
        rewrite HEq in is_sub; simpl in is_sub; trivial.
    }
    {
        move=> eL HRec is_sub [HEq|is_subl]; auto.
        rewrite HEq in is_sub; simpl in is_sub; trivial.
    }
    {
        move=> eL HRec is_sub [HEq|is_subl]; auto.
        rewrite HEq in is_sub; simpl in is_sub; trivial.
    }
    {
        move=> expr HRec; simpl.
        move=> is_sub [HEq|]; auto.
        symmetry in HEq; destruct HEq; simpl in is_sub; auto.
    }
    {
        move=> lop ea HReca eb HRecb is_sub.
        move=> [HEq|[is_suba|is_subb]]; auto.
        by rewrite HEq in is_sub; auto.
    }
    {
        move=> aop ea HReca eb HRecb is_sub.
        move=> [HEq|[is_suba|is_subb]]; auto.
        by rewrite HEq in is_sub; auto.
    }
    {
        move=> sop e HRec ae is_sub [HEq|is_sub']; auto.
        rewrite HEq in is_sub; simpl in is_sub; trivial.
    }
    {
        move=> v l is_sub [HEq|is_sub'].
        by rewrite HEq in is_sub; simpl in is_sub.
        destruct is_sub'; simpl in *.
        destruct is_sub as [->|[]]; auto.
    }
    {
        move=> e HRec ae is_sub [HEq|is_sub']; auto.
        rewrite HEq in is_sub; simpl in is_sub; trivial.
    }
    {
        move=> ea HReca eb HRecb otyp is_sub.
        move=> [HEq|[is_suba|is_subb]]; auto.
        by rewrite HEq in is_sub; auto.
    }
    {
        move=> i eL HRec is_sub [HEq|is_subl]; auto.
        rewrite HEq in is_sub; simpl in is_sub; trivial.
    }
    {
        move=> i ae eL HRec is_sub [HEq|is_subl]; auto.
        rewrite HEq in is_sub; simpl in is_sub; trivial.
    }
    {
        move=> _ [].
    }
    {
        move=> hd HRec_hd tl HRec_tl is_sub.
        move=> [is_sub_hd|is_sub_tl]; auto.
    }
Qed.

Lemma is_subexpr_freefullvars:
    forall e1 e2,
        is_subexpr e1 e2 -> (forall v, In _ (expr_freefullvars e1) v -> In _ (expr_freefullvars e2) v).
Proof.
    move=> e1 e2 is_sub v HIn; move: e2 is_sub.
    refine (expr_find _ (fun exprl =>
        is_subexpr_l e1 exprl -> In _ (exprl_freefullvars exprl) v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); simpl.
    {
        move=> z o [H|[]].
        rewrite H in HIn; simpl in HIn.
        inversion HIn.
    }
    {
        move=> v' [H|[]].
        rewrite H in HIn; simpl in HIn.
        inversion HIn as [HEq]; destruct HEq; assumption.
    }
    {
        move=> el HRec [H|is_sub]; auto.
        rewrite H in HIn; simpl in HIn; assumption.
    }
    {
        move=> el HRec [H|is_sub]; auto.
        rewrite H in HIn; simpl in HIn; assumption.
    }
    {
        move=> e HRec [H|is_sub]; auto.
        rewrite H in HIn; simpl in HIn; assumption.
    }
    {
        move=> op ea HReca eb HRecb [H|[H|H]]; auto.
        by rewrite H in HIn; simpl in HIn; assumption.
        all: by constructor; auto.
    }
    {
        move=> op ea HReca eb HRecb [H|[H|H]]; auto.
        by rewrite H in HIn; simpl in HIn; assumption.
        all: by constructor; auto.
    }
    {
        move=> op e HRec a [H|is_sub]; auto.
        rewrite H in HIn; simpl in HIn; assumption.
    }
    {
        move=> v' l [H|H].
        2: symmetry in H.
        all: rewrite H in HIn; simpl in HIn.
        all: inversion HIn as [HEq]; destruct HEq; assumption.
    }
    {
        move=> e HRec a [H|is_sub]; auto.
        rewrite H in HIn; simpl in HIn; assumption.
    }
    {
        move=> ea HReca eb HRecb top [H|[H|H]]; auto.
        by rewrite H in HIn; simpl in HIn; assumption.
        all: by constructor; auto.
    }
    {
        move=> i el HRec [H|is_sub]; auto.
        rewrite H in HIn; simpl in HIn; assumption.
    }
    {
        move=> i a el HRec [H|is_sub]; auto.
        rewrite H in HIn; simpl in HIn; assumption.
    }
    {
        move=> [].
    }
    {
        by move=> hd HRec_hd tl HRec_tl [is_sub|is_sub]; constructor; auto.
    }
Qed.

(* Ctxt functions soundness *)

Lemma update_ctxt_soundness {A : Type}:
    forall (f : A -> option A) ctxt v,
        distinct (map fst ctxt) ->
        forall ctxt',
            update_ctxt ctxt v f = Some ctxt' ->
            find_val ctxt v <> None /\
            distinct (map fst ctxt') /\
            map fst ctxt = map fst ctxt' /\
            list_rel (fun p1 p2 =>
                p1.1 = p2.1 /\
                if ident_beq p1.1 v
                then f p1.2 = Some p2.2
                else p1.2 = p2.2) ctxt ctxt'.
Proof.
    move=> f ctxt v d; induction ctxt as [|[id val] tl HRec]; simpl in *.
    by idtac.
    move=> ctxt'.
    case_eq (ident_beq v id).
    {
        rewrite ident_beq_eq.
        move=> H; destruct H.
        case_eq (f val); [> move=> val' HEq | by idtac ].
        move=> H; inversion H as [H']; clear H H' ctxt'.
        split; [> by intro | idtac ].
        split; auto.
        split; auto.
        constructor; simpl.
        by rewrite ident_beq_refl; auto.
        inversion d as [|id tl' forall_diff _ H1].
        move: forall_diff; clear.
        induction tl as [|[k val] tl HRec]; simpl.
        by move=> H; constructor.
        move=> H; inversion H as [|hd tl' Hdiff AllDiff].
        constructor; simpl; auto.
        rewrite <-ident_beq_eq in Hdiff; rewrite not_true_iff_false in Hdiff.
        split; trivial.
        rewrite ident_beq_sym in Hdiff; rewrite Hdiff; reflexivity.
    }
    destruct update_ctxt as [c'|].
    2: by idtac.
    inversion d as [|v0 t0 HForall d_tl].
    move: (HRec d_tl c') HForall; clear HRec d d_tl.
    impl_tac; trivial.
    clear.
    move=> [find_val_nNone HRec] HForall.
    move=> neq H; inversion H as [H']; clear H H'.
    split; trivial.
    split.
    {
        destruct HRec as [HRec [HEq _]].
        simpl; constructor; auto.
        rewrite <-HEq; auto.
    }
    split.
    {
        simpl.
        destruct HRec as [_ [-> _]]; auto.
    }
    destruct HRec as [_ [_ HRec]].
    constructor; simpl; auto.
    split; trivial.
    rewrite ident_beq_sym in neq; rewrite neq; reflexivity.
Qed.

Lemma map_ctxt_soundness {A B} (f : A -> B):
    forall v t tctxt,
        List.In (v, t) (map_ctxt f tctxt) ->
            exists t',
                List.In (v, t') tctxt /\
                t = f t'.
Proof.
    move=> v t tctxt.
    induction tctxt as [|[v' t'] tl HRec]; simpl.
    by idtac.
    move=> [H|LIn].
    {
        inversion H.
        eexists; split; [> left; reflexivity | reflexivity ].
    }
    {
        destruct (HRec LIn) as [t'' [LIn' Eq]].
        exists t''; auto.
    }
Qed.

(* properties about undefined *)

Lemma length_undefined {A : Type} :
    forall n, length (@undefined A n) = n.
Proof.
    intro n; induction n as [|n HRec]; simpl; auto.
Qed.

Lemma undefined_sum {A : Type}:
    forall n1 n2,
        @undefined A (n1 + n2) = undefined n1 ++ undefined n2.
Proof.
    intros n n2; induction n as [|n HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Lemma undefined_lemma {A : Type}:
    forall n1 n2,
    concat (map (fun _=> @undefined A n2) (@undefined A n1)) = undefined (n2 * n1)%coq_nat.
Proof.
    intros n1 n2; induction n1 as [|n1 HRec]; simpl.
    {
        rewrite Nat.mul_0_r; auto.
    }
    {
        rewrite Nat.mul_succ_r.
        rewrite Nat.add_comm.
        rewrite undefined_sum.
        rewrite HRec; reflexivity.
    }
Qed.

(* split_into_segments properties *)

Lemma split_into_segments_soundness {A : Type} :
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

Lemma split_into_segments_soundness2 {A : Type} :
    forall i1 i2 l,
        length l = i1 * i2 ->
        exists l', @split_into_segments (option A) i1 i2 (List.map Some l) = Some (List.map (List.map Some) l') /\
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
        pose (p:= take_n_soundness2 i2 l); move: p.
        impl_tac.
        {
            rewrite length_eq; clear.
            rewrite mulSnr.
            apply leq_addl.
        }
        move=> [l1 [l2 [HEq1 [HEq2 LengthEq]]]].
        rewrite HEq1.
        symmetry in HEq2; destruct HEq2.
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

Lemma split_into_segments_1_r {A : Type}:
    forall l : list A, forall n,
        length l = n -> split_into_segments n 1 l = Some (List.map (fun i => [:: i]) l).
Proof.
    move=> l; induction l as [|hd l HRec]; simpl.
    by move=> n <-; simpl; reflexivity.
    move=> [|n].
    by discriminate.
    move=> HEq; inversion HEq; clear HEq; simpl.
    rewrite HRec; auto.
Qed.

Lemma split_into_segments_1_l {A : Type}:
    forall l : list A, forall n,
        length l = n -> split_into_segments 1 n l = Some [:: l].
Proof.
    simpl.
    move=> l n length_eq.
    rewrite take_n_all; trivial.
Qed.


Theorem split_into_segments_undefined {A : Type} :
    forall n1 n2,
        split_into_segments n1 n2 (@undefined A (n1 * n2)) = Some (map (fun _=> undefined n2) (@undefined A n1)).
Proof.
    intro n1; induction n1 as [|n1 HRec]; simpl; trivial.
    intro; rewrite undefined_sum.
    rewrite take_n_sum.
    2: exact (length_undefined _).
    rewrite HRec; reflexivity.
Qed.

(* build_ctxt and auxiliairies properties *)

Theorem build_ctxt_aux_take_n_soundness:
    forall d iL_tl n iL,
        length iL = n ->
        iL_tl <> nil ->
        build_ctxt_aux_take_n n (CoIR d (iL ++ iL_tl) (length iL + length iL_tl::nil)::nil) d
            = Some (iL, CoIR d iL_tl (length iL_tl::nil)::nil).
Proof.
    intros d iL_tl n; induction n as [|n HRec]; simpl.
    all: intros iL; destruct iL as [|hd iL]; simpl; trivial.
    1,2: discriminate.
    rewrite internal_dir_dec_lb0; trivial.
    intro H; inversion H as [HEq]; clear H.
    rewrite try_take_n_soundness; trivial.
    destruct iL_tl; trivial.
    intro H; exfalso; apply H; reflexivity.
Qed.

Theorem build_ctxt_aux_take_n_soundness2:
    forall d n iL form,
        length iL = n ->
        n <> 0 ->
        build_ctxt_aux_take_n n (CoIR d iL form::nil) d
            = Some (iL, nil).
Proof.
    intros d n iL form LengthEq; simpl.
    unfold build_ctxt_aux_take_n.
    rewrite internal_dir_dec_lb0; trivial.
    rewrite try_take_n_all; auto.
    destruct n; trivial.
    intro H; exfalso; apply H; auto.
Qed.

(* Other *)

Lemma zip_rel {A B} {R : A -> B -> Prop}:
    forall l1 l2,
        list_rel_top R l1 l2 <-> Forall (fun p => R p.1 p.2) (zip l1 l2).
Proof.
    move=> l1; induction l1 as [|h1 t1 HRec].
    all: move=> [|h2 l2]; split; simpl; move=> H; inversion H; constructor; auto.
    by rewrite <-HRec; assumption.
    by rewrite HRec; assumption.
Qed.

Theorem remove_option_from_list_map_Some {A : Type}:
    forall l, @remove_option_from_list A (map Some l) = Some l.
Proof.
    intro l; induction l as [|hd tl HRec]; simpl; trivial.
    rewrite HRec; reflexivity.
Qed.

Theorem list_map2_soundness {A B C : Type}:
    forall (f : A -> B -> C) l1 l2, length l1 = length l2 ->
        exists l3, length l3 = length l1 /\ list_map2 f l1 l2 = Some l3.
Proof.
    intros f l1; induction l1 as [|h1 t1 HRec]; simpl.
    {
        intro l2; destruct l2; simpl.
        + intro; exists nil; auto.
        + discriminate.
    }
    {
        intro l2; destruct l2 as [|h2 t2]; simpl.
        { discriminate. }
        intro H; inversion H as [length_eq].
        destruct (HRec _ length_eq) as [l3 [<- ->]].
        exists (f h1 h2::l3); auto.
    }
Qed.

Lemma dir_beq_refl:
    forall d, dir_beq d d = true.
Proof.
    move=> d; destruct d; simpl; trivial.
    all: induction i; simpl; auto.
Qed.
