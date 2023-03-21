From Usuba Require Import usuba_AST usuba_sem.
From mathcomp Require Import all_ssreflect.
Require Setoid.
Require Import RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
From Coq Require Import Bool.Bool.

Section Rel.

Context { arch : architecture}.

Definition expr_rel (e1 e2 : expr) :=
    forall prog ctxt, eval_expr arch prog ctxt e1 = eval_expr arch prog ctxt e2.

Definition context_rel (c1 c2 : context) :=
    forall i : ident, find_val c1 i = find_val c2 i.

Definition context_srel (s : Ensemble ident) (c1 c2 : context) :=
    forall i : ident, In ident s i -> find_val c1 i = find_val c2 i.

Definition opt_rel {A : Type} (R : A -> A -> Prop) (e1 e2 : option A) : Prop :=
    match e1 with
        | None => e2 = None
        | Some e1' => match e2 with
            | None => False
            | Some e2' => R e1' e2'
        end
    end.

Definition deq_rel (d1 d2 : deq) :=
    forall prog ctxt, opt_rel context_rel (eval_deq arch prog ctxt d1) (eval_deq arch prog ctxt d2).

Definition deqs_rel (dl1 dl2 : list_deq) :=
    forall prog ctxt, opt_rel context_rel (eval_deq_list arch prog ctxt dl1) (eval_deq_list arch prog ctxt dl2).

(* Properties on relations *)

Lemma expr_rel_refl:
    forall x, expr_rel x x.
Proof.
    unfold expr_rel; auto.
Qed.

Lemma expr_rel_sym:
    forall x y, expr_rel x y -> expr_rel y x.
Proof.
    unfold expr_rel; auto.
Qed.

Lemma expr_rel_trans:
    forall x y z, expr_rel x y -> expr_rel y z -> expr_rel x z.
Proof.
    unfold expr_rel; auto.
    move=> x y z Eq1 Eq2 prog ctxt.
    rewrite Eq1; auto.
Qed.

#[global]
Instance Refl_expr_rel : Reflexive expr_rel.
Proof. exact expr_rel_refl. Qed.
#[global]
Instance Trans_expr_rel : Transitive expr_rel.
Proof. exact expr_rel_trans. Qed.
#[global]
Instance Sym_expr_rel : Symmetric expr_rel.
Proof. exact expr_rel_sym. Qed.

Lemma context_rel_refl:
    forall c, context_rel c c.
Proof. unfold context_rel; reflexivity. Qed.

Lemma context_rel_sym:
    forall c c', context_rel c c' -> context_rel c' c.
Proof. unfold context_rel; auto. Qed.

Lemma context_rel_trans:
    forall c1 c2 c3, context_rel c1 c2 -> context_rel c2 c3 -> context_rel c1 c3.
Proof.
    unfold context_rel.
    move=> c1 c2 c3 Eq1 Eq2 i; rewrite Eq1; auto.
Qed.

#[global]
Instance Refl_context_rel : Reflexive context_rel.
Proof. exact context_rel_refl. Qed.
#[global]
Instance Trans_context_rel : Transitive context_rel.
Proof. exact context_rel_trans. Qed.
#[global]
Instance Sym_context_rel : Symmetric context_rel.
Proof. exact context_rel_sym. Qed.

Lemma context_srel_refl:
    forall s c, context_srel s c c.
Proof. unfold context_srel; reflexivity. Qed.

Lemma context_srel_sym:
    forall s c c', context_srel s c c' -> context_srel s c' c.
Proof.
    move=> s c c'; unfold context_srel.
    move=> HEq i HIn; rewrite HEq; auto.    
Qed.

Lemma context_srel_trans:
    forall s c1 c2 c3, context_srel s c1 c2 -> context_srel s c2 c3 -> context_srel s c1 c3.
Proof.
    unfold context_srel.
    move=> s c1 c2 c3 Eq1 Eq2 i HIn; rewrite Eq1; auto.
Qed.

#[global]
Instance Refl_context_srel s : Reflexive (context_srel s).
Proof. exact (context_srel_refl _). Qed.
#[global]
Instance Trans_context_srel s : Transitive (context_srel s).
Proof. exact (context_srel_trans _). Qed.
#[global]
Instance Sym_context_srel s : Symmetric (context_srel s).
Proof. exact (context_srel_sym _). Qed.

#[global]
Program Instance Refl_opt_rel {A : Type} (R : A -> A -> Prop) (RR : Reflexive R): Reflexive (opt_rel R).
Next Obligation. unfold opt_rel. case x; auto. Qed.
#[global]
Program Instance Trans_opt_rel {A : Type} (R : A -> A -> Prop) (RR : Transitive R): Transitive (opt_rel R).
Next Obligation.
    unfold opt_rel in *.
    destruct x; destruct y; destruct z; auto.
    + apply (@transitivity _ _ _ a a0 a1); assumption.
    + discriminate.
    + discriminate.
Qed.
#[global]
Program Instance Sym_opt_rel {A : Type} (R : A -> A -> Prop) (RR : Symmetric R): Symmetric (opt_rel R).
Next Obligation.
    unfold opt_rel in *.
    destruct x; destruct y; auto.
    + destruct H.
    + discriminate.
Qed.

Lemma deq_rel_refl: forall d, deq_rel d d.
Proof. unfold deq_rel; reflexivity. Qed.

Lemma deq_rel_sym: forall d1 d2, deq_rel d1 d2 -> deq_rel d2 d1.
Proof. unfold deq_rel; intros; symmetry; auto. Qed.

Lemma deq_rel_trans: forall d1 d2 d3, deq_rel d1 d2 -> deq_rel d2 d3 -> deq_rel d1 d3.
Proof.
    unfold deq_rel; move=> d1 d2 d3 Eq1 Eq2 prog ctxt.
    transitivity (eval_deq arch prog ctxt d2); auto.
Qed.

#[global]
Instance Refl_deq_rel : Reflexive deq_rel.
Proof. exact deq_rel_refl. Qed.
#[global]
Instance Trans_deq_rel : Transitive deq_rel.
Proof. exact deq_rel_trans. Qed.
#[global]
Instance Sym_deq_rel : Symmetric deq_rel.
Proof. exact deq_rel_sym. Qed.

Lemma deqs_rel_refl: forall d, deqs_rel d d.
Proof. unfold deqs_rel; reflexivity. Qed.

Lemma deqs_rel_sym: forall d1 d2, deqs_rel d1 d2 -> deqs_rel d2 d1.
Proof. unfold deqs_rel; intros; symmetry; auto. Qed.

Lemma deqs_rel_trans: forall d1 d2 d3, deqs_rel d1 d2 -> deqs_rel d2 d3 -> deqs_rel d1 d3.
Proof.
    unfold deqs_rel; move=> d1 d2 d3 Eq1 Eq2 prog ctxt.
    transitivity (eval_deq_list arch prog ctxt d2); auto.
Qed.

#[global]
Instance Refl_deqs_rel : Reflexive deqs_rel.
Proof. exact deqs_rel_refl. Qed.
#[global]
Instance Trans_deqs_rel : Transitive deqs_rel.
Proof. exact deqs_rel_trans. Qed.
#[global]
Instance Sym_deqs_rel : Symmetric deqs_rel.
Proof. exact deqs_rel_sym. Qed.

End Rel.

(* Properties on context_srel and opt_rel *)


Lemma context_srel_Union_switch:
    forall s1 s2 s3 c1 c2,
        context_srel (Union ident (Union ident s1 s2) s3) c1 c2 <-> 
        context_srel (Union ident s1 (Union ident s2 s3)) c1 c2.
Proof.
    move=> s1 s2 s3 c1 c2; split; move=> HRel x HIn; apply HRel; destruct HIn as [x HIn| x HIn].
    + do 2 constructor; assumption.
    + destruct HIn.
        - do 2 constructor; assumption.
        - constructor; assumption.
    + destruct HIn.
        - constructor; assumption.
        - do 2 constructor; assumption.
    + do 2 constructor; assumption.
Qed.

Lemma context_srel_Union1_comm:
    forall s1 s2 s3 c1 c2,
        context_srel (Union ident (Union ident s1 s2) s3) c1 c2 <-> 
        context_srel (Union ident (Union ident s2 s1) s3) c1 c2.
Proof.
    move=> s1 s2 s3 c1 c2; split; move=> HRel x HIn; apply HRel; destruct HIn as [x HIn| x HIn].
    + destruct HIn; do 2 constructor; assumption.
    + constructor; assumption.
    + destruct HIn; do 2 constructor; assumption.
    + constructor; assumption.
Qed.

Lemma context_srel_Union2_comm:
    forall s1 s2 s3 c1 c2,
        context_srel (Union ident s1 (Union ident s2 s3)) c1 c2 <-> 
        context_srel (Union ident s1 (Union ident s3 s2)) c1 c2.
Proof.
    move=> s1 s2 s3 c1 c2; split; move=> HRel x HIn; apply HRel; destruct HIn as [x HIn| x HIn].
    + constructor; assumption.
    + destruct HIn; do 2 constructor; assumption.
    + constructor; assumption.
    + destruct HIn; do 2 constructor; assumption.
Qed.

Lemma opt_rel_context_srel_change_set:
    forall s1 s2,
        (forall c1 c2, context_srel s1 c1 c2 <-> context_srel s2 c1 c2) ->
        forall o1 o2, opt_rel (context_srel s1) o1 o2 <-> opt_rel (context_srel s2) o1 o2.
Proof.
    move=> s1 s2 Hypo [c1|] [c2|]; split; simpl; trivial.
    all: rewrite Hypo; trivial.
Qed.


Lemma context_srel_bind_compl:
    forall var val ctxt,
        match bind ctxt var val with
        | Some ctxt' => context_srel (Complement ident (var_freevars var)) ctxt ctxt'
        | None => True
        end.
Proof.
    move=> var.
    eapply (var_find (fun var => forall val ctxt, match bind ctxt var val with | Some ctxt' => context_srel (Complement ident (var_freevars var)) ctxt ctxt' | None => True end)
        (fun varL => forall valL ctxt, match bind_list ctxt varL valL with
            | Some ctxt' => context_srel (Complement ident (varl_freevars varL)) ctxt ctxt'
            | None => True end) _ _ _ _ _ _ _ var).
    Unshelve.
    all: clear var; simpl.
    {
        move=> l HRec [| | valL] ctxt; simpl; trivial.
        exact (HRec _ _).
    }
    {
        move=> i val ctxt x HIn; simpl.
        case_eq (String.eqb x i); simpl; trivial.
        rewrite String.eqb_eq; move=> HEq; destruct HEq.
        destruct HIn; constructor.
    }
    {
        move=> []; simpl; trivial.
        move=> i HRec ae val ctxt.
        destruct (eval_arith_expr ctxt ae) as [n|]; simpl; trivial.
        destruct (find_val ctxt i) as [[| |l]|]; simpl; trivial.
        destruct (replace_id n l val) as [v'|]; simpl; trivial.
        move=> x HIn; apply HRec.
        unfold Complement; unfold In; move=> HIn'.
        destruct HIn.
        constructor; assumption.
    }
    {
        trivial.
    }
    {
        trivial.
    }
    {
        move=> []; simpl; trivial.
        reflexivity.
    }
    {
        move=> varHD HRec varTL HRecL [|valHD valTL] ctxt; simpl; trivial.
        specialize HRec with valHD ctxt.
        destruct (bind ctxt varHD valHD) as [ctxt'|]; trivial.
        specialize HRecL with valTL ctxt'.
        destruct (bind_list ctxt' varTL valTL) as [ctxt'2|]; trivial.
        transitivity ctxt'.
        + move=> x HIn; apply HRec.
            unfold Complement; unfold In; move=> HIn'; destruct HIn.
            constructor; assumption.
        + move=> x HIn; apply HRecL.
            unfold Complement; unfold In; move=> HIn'; destruct HIn.
            constructor; assumption.
    }
Qed.

(* Properties about changing context *)

Lemma loop_rec_eta_Some:
    forall i1 i2 i ctxt,
        opt_rel (context_srel (Complement ident (Singleton ident i))) (loop_rec ctxt [eta Some] i i1 i2) (Some ctxt).
Proof.
    move=> i1 i2; induction i2 as [|i2 HRec]; simpl.
    by reflexivity.
    case (match i1 with 0 => false | m'.+1 => PeanoNat.Nat.leb i2 m' end).
    by reflexivity.
    move=> i ctxt; specialize HRec with i ctxt.
    destruct (loop_rec ctxt [eta Some] i i1 i2); simpl in *; trivial.
    move=> x HIn; simpl.
    case_eq (String.eqb x i); trivial.
    + rewrite String.eqb_eq; move=> HEq; destruct HEq.
        destruct HIn; constructor.
    + move=> Snebq; apply HRec; assumption.
Qed.

Theorem expr_rel_IMP_deq_rel (arch : architecture):
    forall e1 e2 vl b, @expr_rel arch e1 e2 -> @deq_rel arch (Eqn vl e1 b) (Eqn vl e2 b).
Proof.
    move=> e1 e2 vl b expr_eq.
    unfold deq_rel; simpl.
    unfold expr_rel in expr_eq; simpl in expr_eq.
    intros; rewrite expr_eq.
    apply reflexivity.
Qed.

Theorem find_val_imp_find_const:
    forall x ctxt1 ctxt2,
        find_val ctxt1 x = find_val ctxt2 x -> find_const ctxt1 x = find_const ctxt2 x.
Proof.
    move=> x ctxt1.
    induction ctxt1 as [|[n1 v1] ctxt1 HRec1]; simpl.
    {
        move=> ctxt2; induction ctxt2 as [|[n v] tl HRec]; simpl; trivial.
        case (String.eqb x n).
        + discriminate.
        + assumption.
    }
    {
        move=> ctxt2.
        case (String.eqb x n1); auto.
        induction ctxt2 as [|[n2 v2] ctxt2 HRec2]; simpl.
        + discriminate.
        + case (String.eqb x n2).
            - move=> HEq; inversion HEq; reflexivity.
            - assumption.
    }
Qed.

Theorem eval_aexpr_change_ctxt:
    (forall e ctxt1 ctxt2,
        (forall x, In ident (aexpr_freevars e) x -> find_const ctxt1 x = find_const ctxt2 x) ->
        eval_arith_expr ctxt1 e = eval_arith_expr ctxt2 e).
Proof.
    move=> e; induction e as [| |op e1 HRec1 e2 HRec2]; simpl; trivial.
    {
        move=> c1 c2 HImpl; apply HImpl.
        constructor.
    }
    {
        move=> ctxt1 ctxt2 HImpl.
        rewrite (HRec1 ctxt1 ctxt2).
        2: move=> x HIn; apply HImpl; constructor; assumption.
        rewrite (HRec2 ctxt1 ctxt2).
        2: move=> x HIn; apply HImpl; constructor; assumption.
        reflexivity.
    }
Qed.

Ltac eq_match :=
    lazymatch goal with
    | |- match ?A with Some _ => _ | None => _ end = match ?B with Some _ => _ | None => _  end =>
        let H := fresh "H" in
        assert (A = B) as H; [> idtac | rewrite H; reflexivity]
    end.

Theorem eval_var_change_ctxt:
    (forall v ctxt1 ctxt2,
        context_srel (var_freevars v) ctxt1 ctxt2 ->
        eval_var ctxt1 v = eval_var ctxt2 v).
Proof.
    apply (var_find
        (fun v => forall ctxt1 ctxt2,
            context_srel (var_freevars v) ctxt1 ctxt2 ->
            eval_var ctxt1 v = eval_var ctxt2 v)
        (fun v => forall ctxt1 ctxt2,
            context_srel (varl_freevars v) ctxt1 ctxt2 ->
            eval_vars ctxt1 v = eval_vars ctxt2 v)); simpl.
    + move=> l HRec ctxt1 ctxt2 HImpl; rewrite (HRec ctxt1 ctxt2).
        - reflexivity.
        - move=> x HIn; apply HImpl; assumption.
    + move=> i ctxt1 ctxt2 ->; trivial.
        - constructor.
    + move=> v HRec ae ctxt1 ctxt2 HContent; rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        - rewrite (HRec ctxt1 ctxt2).
            * reflexivity.
            * move=> x HIn; apply HContent; constructor; assumption.
        - move=> x HIn; apply find_val_imp_find_const; apply HContent; constructor; assumption.
    + move=> v HRec ae1 ae2 ctxt1 ctxt2 HContent; rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        - rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
            * rewrite (HRec ctxt1 ctxt2); trivial.
                by move=> x HIn; apply HContent; constructor; assumption.
            * move=> x HIn; apply find_val_imp_find_const; apply HContent; do 2 constructor; assumption.
        - move=> x HIn; apply find_val_imp_find_const; apply HContent; do 2 constructor; assumption.
    + move=> v HRec ael ctxt1 ctxt2 HContent.
        rewrite (HRec ctxt1 ctxt2).
        2: by move=> x HIn; apply HContent; constructor; assumption.
        eq_match.
        clear HRec.
        move: HContent.
        induction ael as [|a tl HRec]; simpl; trivial.
        move=> HContent.
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: by move=> x HIn; apply find_val_imp_find_const; apply HContent; constructor; constructor; assumption.
        eq_match.
        apply HRec.
        move=> x HIn; apply HContent; inversion HIn.
        - constructor; assumption.
        - do 2 constructor; assumption.
    + reflexivity.
    + move=> v HRec vL HRecL ctxt1 ctxt2 HContent; rewrite (HRec ctxt1 ctxt2).
        - rewrite (HRecL ctxt1 ctxt2); trivial.
            * move=> x HIn; apply HContent; constructor; assumption.
        - move=> x HIn; apply HContent; constructor; assumption.
Qed.

Theorem eval_expr_change_ctxt (arch : architecture) (prog : prog_ctxt):
    (forall e ctxt1 ctxt2,
        (context_srel (expr_freevars e) ctxt1 ctxt2) ->
        eval_expr arch prog ctxt1 e = eval_expr arch prog ctxt2 e).
Proof.
    apply (expr_find
        (fun e => forall ctxt1 ctxt2,
            context_srel (expr_freevars e) ctxt1 ctxt2 ->
            eval_expr arch prog ctxt1 e = eval_expr arch prog ctxt2 e)
        (fun el => forall ctxt1 ctxt2,
            context_srel (exprl_freevars el) ctxt1 ctxt2 ->
            eval_expr_list arch prog ctxt1 el = eval_expr_list arch prog ctxt2 el)); simpl.
    + reflexivity.
    + intros; apply eval_var_change_ctxt. assumption.
    + move=> e' HRec ctxt1 ctxt2 HContent. rewrite (HRec ctxt1 ctxt2 HContent); reflexivity.
    + move=> e' HRec ctxt1 ctxt2 HContent; rewrite (HRec ctxt1 ctxt2 HContent); reflexivity.
    + move=> op e1 HRec1 e2 HRec2 ctxt1 ctxt2 HContent; rewrite (HRec1 ctxt1 ctxt2).
        - rewrite (HRec2 ctxt1 ctxt2).
            * reflexivity.
            * move=> x HIn; apply HContent; constructor; assumption.
        - move=> x HIn; apply HContent; constructor; assumption.
    + move=> op e1 HRec1 e2 HRec2 ctxt1 ctxt2 HContent; rewrite (HRec1 ctxt1 ctxt2).
        - rewrite (HRec2 ctxt1 ctxt2).
            * reflexivity.
            * move=> x HIn; apply HContent; constructor; assumption.
        - move=> x HIn; apply HContent; constructor; assumption.
    + move=> op e1 HRec1 a ctxt1 ctxt2 HContent; rewrite (HRec1 ctxt1 ctxt2).
        - rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
            * reflexivity.
            * move=> x HIn; apply find_val_imp_find_const; apply HContent; constructor; assumption.
        - move=> x HIn; apply HContent; constructor; assumption.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + move=> fname el HRec ctxt1 ctxt2 HContent; rewrite (HRec ctxt1 ctxt2).
        - reflexivity.
        - move=> x HIn; apply HContent; constructor; assumption.
    + move=> fname ae el HRec ctxt1 ctxt2 HContent; rewrite (HRec ctxt1 ctxt2).
        - rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
            * reflexivity.
            * move=> x HIn; apply find_val_imp_find_const; apply HContent; do 2 constructor; assumption.
        - move=> x HIn; apply HContent; do 2 constructor; assumption.
    + reflexivity.
    + move=> e' HRec el HRecL ctxt1 ctxt2 HContent.
        rewrite (HRec ctxt1 ctxt2).
        2: move=> x HIn; apply HContent; constructor; assumption.
        rewrite (HRecL ctxt1 ctxt2); trivial.
        move => x HIn; apply HContent; constructor; assumption.
Qed.

Lemma context_srel_bind:
    forall var ctxt1 ctxt2 val s,
        context_srel (Union ident (var_freevars var) s) ctxt1 ctxt2 ->
            opt_rel (context_srel (Union ident (var_freevars var) s)) (bind ctxt1 var val) (bind ctxt2 var val).
Proof.
    move=> var.
    eapply (var_find (fun var => forall (ctxt1 ctxt2 : context) (val : Value) (s : Ensemble ident),
        context_srel (Union ident (var_freevars var) s) ctxt1 ctxt2 -> opt_rel (context_srel (Union ident (var_freevars var) s))
        (bind ctxt1 var val) (bind ctxt2 var val)) (fun varl => forall (ctxt1 ctxt2 : context) (valL : list_Value) (s : Ensemble ident),
            context_srel (Union ident (varl_freevars varl) s) ctxt1 ctxt2 -> opt_rel (context_srel (Union ident (varl_freevars varl) s)) (bind_list ctxt1 varl valL) (bind_list ctxt2 varl valL)) _ _ _ _ _ _ _ var).
    Unshelve.
    all: simpl.
    {
        move=> l HRec ctxt1 ctxt2 []; simpl; trivial.
        move=> vL s HRel; apply HRec; auto.
    }
    {
        move=> i ctxt1 ctxt2 val s HRel x HIn; simpl.
        case (String.eqb x i); simpl; trivial.
        apply HRel; assumption.
    }
    {
        move=> []; simpl; trivial.
        move=> i HRec ae ctxt1 ctxt2 val s HRel.
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: by move=> x HIn; apply find_val_imp_find_const; apply HRel; do 2 constructor; assumption.
        rewrite (HRel i).
        2: by do 3 constructor; assumption.
        case (eval_arith_expr ctxt2 ae); simpl; trivial; move=> n.
        case (find_val ctxt2 i); simpl; trivial.
        move=> []; simpl; trivial.
        move=> l; case (replace_id n l val); simpl; trivial.
        move=> l0 x HIn; simpl.
        case (String.eqb x i); trivial.
        apply HRel; trivial.
    }
    {
        reflexivity.
    }
    {
        reflexivity.
    }
    {
        move=> ctxt1 ctxt2 []; simpl; trivial.
    }
    {
        move=> v HRec l HRecL ctxt1 ctxt2 []; simpl; trivial.
        move=> valHD valTL s HRel.
        assert (context_srel (Union ident (var_freevars v) (Union ident s (varl_freevars l))) ctxt1 ctxt2) as HRel'.
        { 
            move=> x HIn; apply HRel; destruct HIn as [|x HIn].
                + do 2 constructor; assumption.
                + destruct HIn.
                    - constructor; assumption.
                    - do 2 constructor; assumption.
        }
        pose (p := HRec _ _ valHD _ HRel'); move:p.
        case (bind ctxt1 v valHD); simpl.
        2: by move=> ->; simpl; reflexivity.
        case (bind ctxt2 v valHD); simpl.
        2: by move=> _ [].
        clear HRec HRel HRel' valHD var ctxt1 ctxt2.
        move=> ctxt1 ctxt2 HRel.
        rewrite (opt_rel_context_srel_change_set _ _ (context_srel_Union1_comm _ _ _) _ _).
        rewrite (opt_rel_context_srel_change_set _ _ (context_srel_Union_switch _ _ _) _ _).
        apply HRecL.
        rewrite <- context_srel_Union_switch.
        rewrite context_srel_Union1_comm.
        rewrite context_srel_Union_switch.
        rewrite context_srel_Union2_comm.
        assumption.
    }
Qed.

Theorem fold_left_equal {A B : Type} :
    forall f1 f2 : A -> B -> A,
        (forall a1 a2, f1 a1 a2 = f2 a1 a2) -> 
        forall (l : list B), forall init : A, fold_left f1 l init = fold_left f2 l init.
Proof.
    move=> f1 f2 HEq l; induction l as [|h l HRec]; simpl; trivial.
    move=> init; rewrite HEq; rewrite HRec; trivial.
Qed.

Lemma loop_rec_equiv:
    forall f1 f2,
        (forall a, f1 a = f2 a) ->
        forall s e init i,
            loop_rec init f1 i s e = loop_rec init f2 i s e.
Proof.
    move=> f1 f2 HEq s e; induction e; simpl; trivial.
    move=> init i.
    rewrite IHe; case (loop_rec init f2 i s e).
    + intro; rewrite HEq; reflexivity.
    + reflexivity.
Qed.

Inductive deqL :=
    | DLnil
    | DLEqn : var -> expr -> bool -> deqL -> deqL
    | DLLoop : ident -> arith_expr -> arith_expr -> deqL -> list stmt_opt -> deqL -> deqL.

Fixpoint deqL_of_list_deq (d : list_deq) : deqL :=
    match d with
    | Dnil => DLnil
    | Dcons (Eqn v e b) tl => DLEqn v e b (deqL_of_list_deq tl)
    | Dcons (Loop i e1 e2 body opt) tl => DLLoop i e1 e2 (deqL_of_list_deq body) opt (deqL_of_list_deq tl)
    end.

Fixpoint list_deq_of_deqL (d : deqL) : list_deq :=
    match d with
    | DLnil => Dnil
    | DLEqn v e b tl => Dcons (Eqn v e b) (list_deq_of_deqL tl)
    | DLLoop i e1 e2 body opt tl => Dcons (Loop i e1 e2 (list_deq_of_deqL body) opt) (list_deq_of_deqL tl)
    end.

    Lemma deqL_is_list_deq:
    forall ld,
        list_deq_of_deqL (deqL_of_list_deq ld) = ld.
Proof.
    move=> ld.
    refine (list_deq_find (fun d => list_deq_of_deqL (deqL_of_list_deq (Dcons d Dnil)) = (Dcons d Dnil)) (fun ld => _ = _) _ _ _ _ ld); simpl; trivial.
    {
        move=> i a1 a2 l ->; reflexivity.
    }
    {
        move=> [v e b|i a1 a2 body opt]; simpl; move=> HEq; inversion HEq as [HEq'].
        all: move=> l ->; trivial.
        do 2 rewrite HEq'; trivial.
    }
Qed.

Lemma eval_deqL_change_ctxt arch prog:
    forall eqns ctxt1 ctxt2 s,
        (forall elt, In ident (deqs_vars (list_deq_of_deqL eqns)) elt -> In ident s elt)
        -> context_srel s ctxt1 ctxt2
        -> opt_rel (context_srel s)
            (eval_deq_list arch prog ctxt1 (list_deq_of_deqL eqns))
            (eval_deq_list arch prog ctxt2 (list_deq_of_deqL eqns)).
Proof.
    move=> eqns; induction eqns as [|v e b tl HRec|i a1 a2 body HRecBody opt tl HRecTL]; simpl; auto.
    {
        move=> ctxt1 ctxt2 s HSubset HRel.
        rewrite (eval_expr_change_ctxt _ _ _ ctxt1 ctxt2).
        2: by move=> x HIn; apply HRel; apply HSubset; do 2 constructor; assumption.
        destruct (eval_expr arch prog ctxt2 e) as [val|].
        2: reflexivity.
        assert (context_srel (Union ident (var_freevars v) s) ctxt1 ctxt2) as HRel'
        by (move=> x [x' HIn|x' HIn]; apply HRel; trivial; apply HSubset; do 2 constructor; assumption).
        pose (p := context_srel_bind _ _ _ val _ HRel'); move:p; clear HRel'.
        destruct (bind ctxt1 v val) as [ctxt1'|]; destruct (bind ctxt2 v val) as [ctxt2'|]; simpl.
        2: move=> [].
        2: discriminate.
        2: reflexivity.
        move=> HRel'; apply HRec.
        + move=> x HIn; apply HSubset; constructor; assumption.
        + move=> x HIn; apply HRel'; constructor; assumption.
    }
    {
        move=> ctxt1 ctxt2 s HSubset HRel.
        rewrite (eval_aexpr_change_ctxt a1 ctxt1 ctxt2).
        2: move=> x HIn; apply find_val_imp_find_const; apply HRel; apply HSubset; do 3 constructor; assumption.
        rewrite (eval_aexpr_change_ctxt a2 ctxt1 ctxt2).
        2: move=> x HIn; apply find_val_imp_find_const; apply HRel; apply HSubset; do 4 constructor; assumption.
        destruct (eval_arith_expr ctxt2 a1) as [i1|]; simpl; trivial.
        destruct (eval_arith_expr ctxt2 a2) as [i2|]; simpl; trivial.
        assert (opt_rel (context_srel s)
                (loop_rec ctxt1 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2)
                (loop_rec ctxt2 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2))
            as HLoop.
        {
            assert (forall elt, In ident (deqs_vars (list_deq_of_deqL body)) elt -> In ident s elt) as HSubset'
                by (move=> elt HIn; apply HSubset; do 4 constructor; assumption).
            clear HSubset HRecTL a1 a2 tl.
            induction i2 as [|i2 HReci]; simpl; auto.
            case (match i1 with 0 => false | m'.+1 => PeanoNat.Nat.leb i2 m' end); simpl; trivial.
            destruct (loop_rec ctxt1 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt1'|].
            2: simpl in HReci; rewrite HReci; reflexivity.
            destruct (loop_rec ctxt2 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt2'|].
            all: simpl in HReci.
            2: by destruct HReci.
            apply HRecBody; trivial.
            move=> x HIn; simpl.
            case (String.eqb x i); trivial; apply HReci; assumption.
        }
        destruct (loop_rec ctxt1 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt1'|].
        2: simpl in HLoop; rewrite HLoop; reflexivity.
        destruct (loop_rec ctxt2 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt2'|].
        all: simpl in HLoop.
        2: by destruct HLoop.
        assert (match find_val ctxt1 i with Some v => Some ((i, v) :: ctxt1') | None => Some ctxt1' end
            = Some match find_val ctxt1 i with Some v => (i, v)::ctxt1' | None => ctxt1' end) as HEq
            by (case (find_val ctxt1 i); simpl; auto).
        rewrite HEq; clear HEq.
        assert (match find_val ctxt2 i with Some v => Some ((i, v) :: ctxt2') | None => Some ctxt2' end
            = Some match find_val ctxt2 i with Some v => (i, v)::ctxt2' | None => ctxt2' end) as HEq
            by (case (find_val ctxt2 i); simpl; auto).
        rewrite HEq; clear HEq.
        apply HRecTL.
        1: by move=> elt HIn; apply HSubset; constructor; assumption.
        move=> elt HIn.
        case_eq (String.eqb elt i).
        {
            rewrite String.eqb_eq; move=> HEq; destruct HEq.
            pose (HEq := HRel elt HIn).
            rewrite HEq.
            case (find_val ctxt2 elt); simpl.
            + rewrite String.eqb_refl; reflexivity.
            + apply HLoop; assumption.
        }
        {
            case (find_val ctxt1 i); case (find_val ctxt2 i); simpl.
            move=> v v' ->.
            2,3: move=> v ->.
            4: move=> _.
            all: apply HLoop; assumption.
        }
    }
Qed.


Lemma eval_deq_list_unchanged_ctxt arch prog:
    forall eqns ctxt,
        match eval_deq_list arch prog ctxt (list_deq_of_deqL eqns) with
        | None => True
        | Some ctxt' => context_srel (Complement ident (deqs_boundvars (list_deq_of_deqL eqns))) ctxt ctxt'
        end.
Proof.
    move=> eqns; induction eqns as [|var e b tl HRecTL| i a1 a2 body HRecBody opt tl HRecTL]; simpl.
    { reflexivity. }
    {
        move=> ctxt.
        destruct (eval_expr arch prog ctxt e) as [val|]; simpl; trivial.
        pose (p := context_srel_bind_compl var val ctxt); move:p.
        destruct (bind ctxt var val) as [ctxt'|]; simpl; trivial.
        specialize HRecTL with ctxt'.
        destruct (eval_deq_list arch prog ctxt' (list_deq_of_deqL tl)) as [ctxt'2|]; trivial.
        move=> HRel; transitivity ctxt'; move=> x HIn.
        + apply HRel; unfold Complement; unfold In; move=> not_var.
            destruct HIn; constructor 1; unfold In; assumption.
        + apply HRecTL; unfold Complement; unfold In; move=> not_var.
            destruct HIn; constructor 2; unfold In; assumption.
    }
    {
        move=> ctxt.
        destruct (eval_arith_expr ctxt a1) as [i1|]; simpl; trivial.
        destruct (eval_arith_expr ctxt a2) as [i2|]; simpl; trivial.
        assert (match loop_rec ctxt ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2 with
            | None => True
            | Some ctxt' => context_srel (Complement ident (Union ident (Singleton ident i) (deqs_boundvars (list_deq_of_deqL body)))) ctxt ctxt'
            end) as HLoop.
        {
            clear HRecTL tl a1 a2; induction i2 as [|i2 HReci]; simpl.
            { reflexivity. }
            case (match i1 with 0 => false | m'.+1 => PeanoNat.Nat.leb i2 m' end).
            { reflexivity. }
            destruct (loop_rec ctxt ((eval_deq_list arch prog)^~(list_deq_of_deqL body)) i i1 i2) as [ctxt'|]; trivial.
            specialize HRecBody with ((i, VConst i2) :: ctxt').
            destruct (eval_deq_list arch prog ((i, VConst i2)::ctxt') (list_deq_of_deqL body)) as [ctxt'2|]; trivial.
            transitivity ctxt'; trivial.
            move=> elt HIn; rewrite <- HRecBody.
            + simpl.
                assert (String.eqb elt i = false) as HEq.
                2: by rewrite HEq; reflexivity.
                rewrite <- not_true_iff_false; rewrite String.eqb_eq; move=> HEq; destruct HEq.
                destruct HIn; do 2 constructor 1.
            + unfold Complement, In; intro; destruct HIn; constructor 2; unfold In; assumption.
        }
        clear HRecBody.
        destruct (loop_rec ctxt ((eval_deq_list arch prog)^~(list_deq_of_deqL body)) i i1 i2) as [ctxt'|]; trivial.
        specialize HRecTL with (match find_val ctxt i with Some v => (i,v)::ctxt' | None=> ctxt' end).
        destruct (find_val ctxt i) as [val|].
        {
            destruct (eval_deq_list arch prog ((i, val)::ctxt') (list_deq_of_deqL tl)) as [ctxt'2|]; trivial.
            transitivity ctxt'; move=> x HIn.
            {
                apply HLoop; unfold Complement; unfold In; move=> HProp.
                destruct HIn; destruct HProp as [elt []|].
                + by do 3 constructor.
                + by do 2 constructor; assumption.
            }
            rewrite <- HRecTL.
            + simpl.
                assert (String.eqb x i = false) as HEq.
                2: by rewrite HEq; reflexivity.
                rewrite <- not_true_iff_false; rewrite String.eqb_eq; move=> HEq; destruct HEq.
                destruct HIn; do 3 constructor 1.
            + unfold Complement, In; intro; destruct HIn; constructor 2; unfold In; assumption.
        }
        {
            destruct (eval_deq_list arch prog ctxt' (list_deq_of_deqL tl)) as [ctxt'2|]; trivial.
            transitivity ctxt'; move=> x HIn.
            {
                apply HLoop; unfold Complement; unfold In; move=> HProp.
                destruct HIn; destruct HProp as [elt []|].
                + by do 3 constructor.
                + by do 2 constructor; assumption.
            }
            apply HRecTL.
            unfold Complement, In; intro; destruct HIn.
            constructor 2; unfold In; assumption.
        }
    }
Qed.

Lemma loop_rec_unchanged_ctxt arch prog:
    forall i i1 i2 body ctxt,
        match loop_rec ctxt ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2 with
        | None => True
        | Some ctxt' => context_srel (Complement ident (Union ident (Singleton ident i) (deqs_boundvars (list_deq_of_deqL body)))) ctxt ctxt'
        end.
Proof.
    move=> i i1 i2 body ctxt; induction i2 as [|i2 HRec]; simpl.
    { reflexivity. }
    case (match i1 with 0 => false | m'.+1 => PeanoNat.Nat.leb i2 m' end).
    { reflexivity. }
    destruct (loop_rec ctxt ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt'|]; trivial.
    pose (p := eval_deq_list_unchanged_ctxt arch prog body ((i, VConst i2)::ctxt')); move:p.
    destruct (eval_deq_list arch prog ((i, VConst i2)::ctxt') (list_deq_of_deqL body)) as [ctxt'2|]; trivial.
    move=> HBody; transitivity ctxt'; trivial.
    move=> elt HIn; rewrite <- HBody.
    + simpl.
        assert (String.eqb elt i = false) as HEq.
        2: by rewrite HEq; reflexivity.
        rewrite <- not_true_iff_false; rewrite String.eqb_eq; move=> HEq; destruct HEq.
        destruct HIn; do 2 constructor 1.
    + unfold Complement, In; intro; destruct HIn; constructor 2; unfold In; assumption.
Qed.
