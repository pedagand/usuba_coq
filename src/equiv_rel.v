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
    forall prog type_ctxt ctxt, opt_rel context_rel (eval_deq arch prog type_ctxt ctxt d1) (eval_deq arch prog type_ctxt ctxt d2).

Definition deqs_rel (dl1 dl2 : list_deq) :=
    forall prog type_ctxt ctxt, opt_rel context_rel (eval_deq_list arch prog type_ctxt ctxt dl1) (eval_deq_list arch prog type_ctxt ctxt dl2).

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
    unfold deq_rel; move=> d1 d2 d3 Eq1 Eq2 prog type_ctxt ctxt.
    transitivity (eval_deq arch prog type_ctxt ctxt d2); auto.
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
    unfold deqs_rel; move=> d1 d2 d3 Eq1 Eq2 prog type_ctxt ctxt.
    transitivity (eval_deq_list arch prog type_ctxt ctxt d2); auto.
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

(* Properties about changing context *)

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

Lemma context_s_rel_bind_aux_compl:
    forall var acc val ctxt type_ctxt,
        match bind_aux ctxt type_ctxt var acc val with
            | Some (ctxt', l) => context_srel (Complement ident (var_freevars var)) ctxt ctxt'
            | None => True
        end.
Proof.
    move=> var; induction var as [v|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl.
    all: move=> acc val ctxt type_ctxt.
    {
        destruct (find_val type_ctxt v) as [typ|]; trivial.
        destruct (convert_type typ nil) as [[dir form]|]; trivial.
        pose (iL := match find_val ctxt v with | Some c => match c with | CoIL i => i::nil | CoIR _ iL _ => iL end | None => zeros (prod_list form) end).
        fold iL.
        destruct (update form iL acc val dir) as [[val' e']|]; trivial; clear iL.
        move=> elt HIn; simpl.
        case_eq (String.eqb elt v); trivial.
        rewrite String.eqb_eq; move=> HEq; destruct HEq.
        destruct HIn; constructor.
    }
    {
        destruct (eval_arith_expr ctxt ae) as [i|]; trivial.
        specialize HRec with (AInd i acc) val ctxt type_ctxt.
        destruct (bind_aux ctxt type_ctxt v (AInd i acc) val) as [[ctxt' _]|]; trivial.
        move=> elt HIn; apply HRec.
        unfold In, Complement; move=> HIn'; destruct HIn.
        constructor; assumption.
    }
    {
        destruct (eval_arith_expr ctxt ae1) as [i1|]; trivial.
        destruct (eval_arith_expr ctxt ae2) as [i2|]; trivial.
        specialize HRec with (ARange i1 i2 acc) val ctxt type_ctxt.
        destruct (bind_aux ctxt type_ctxt v (ARange i1 i2 acc) val) as [[ctxt' _]|]; trivial.
        move=> elt HIn; apply HRec.
        unfold In, Complement; move=> HIn'; destruct HIn.
        constructor; assumption.
    }
    {
        pose (f := fun ae l => l' <- l; x' <- eval_arith_expr ctxt ae; Some (x'::l')).
        fold f.
        destruct (fold_right f (Some nil) aeL) as [iL|]; trivial; clear f.
        specialize HRec with (ASlice iL acc) val ctxt type_ctxt.
        destruct (bind_aux ctxt type_ctxt v (ASlice iL acc) val) as [[ctxt' val']|]; trivial.
        move=> elt HIn; apply HRec.
        unfold In, Complement; move=> HIn'; destruct HIn.
        constructor; assumption.
    }
Qed.

Ltac impl_tac :=
    lazymatch goal with
    | |- (?A -> ?B) -> ?C =>
        let H := fresh "H" in
        let H2 := fresh "H" in
        let H3 := fresh "H" in
        assert A as H; [> idtac | (move=> H2; pose (H3 := H2 H); move: H3; clear H2 H)]
    end.

Theorem fold_right_equal {A B : Type} :
    forall f1 f2 : A -> B -> B,
        (forall a1 a2, f1 a1 a2 = f2 a1 a2) -> 
        forall (l : list A), forall init : B, fold_right f1 init l = fold_right f2 init l.
Proof.
    move=> f1 f2 HEq l; induction l as [|h l HRec]; simpl; trivial.
    move=> init; rewrite HEq; rewrite HRec; trivial.
Qed.

Lemma context_s_rel_bind_aux:
    forall var acc type_ctxt ctxt1 ctxt2 val s,
    context_srel (Union ident (var_freevars var) s) ctxt1 ctxt2 ->
        opt_rel (fun p1 p2 => context_srel (Union ident (var_freevars var) s) p1.1 p2.1 /\ p1.2 = p2.2) (bind_aux ctxt1 type_ctxt var acc val) (bind_aux ctxt2 type_ctxt var acc val).
Proof.
    move=> var; induction var as [v|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl.
    all: move=> acc type_ctxt ctxt1 ctxt2 val s HRel.
    {
        destruct (find_val type_ctxt v) as [typ|]; simpl; trivial.
        destruct (convert_type typ nil) as [[dir form]|]; simpl; trivial.
        rewrite (HRel v).
        2: by do 2 constructor.
        pose (iL := match find_val ctxt2 v with | Some c => match c with | CoIL i => i::nil | CoIR _ iL _ => iL end | None => zeros (prod_list form) end).
        fold iL.
        destruct (update form iL acc val dir) as [[val' e']|]; simpl; trivial; clear iL.
        split; trivial.
        move=> elt HIn; simpl.
        case_eq (String.eqb elt v); trivial.
        move=> HEq; apply HRel; assumption.
    }
    {
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: move=> elt HIn; apply find_val_imp_find_const; apply HRel; do 2 constructor; assumption.
        destruct (eval_arith_expr ctxt2 ae) as [i|]; simpl; trivial.
        specialize HRec with (AInd i acc) type_ctxt ctxt1 ctxt2 val (Union ident (aexpr_freevars ae) s).
        move: HRec.
        impl_tac.
        by rewrite <- context_srel_Union_switch; assumption.
        destruct (bind_aux ctxt1 type_ctxt v (AInd i acc) val) as [[ctxt1' l1]|]; trivial.
        destruct (bind_aux ctxt2 type_ctxt v (AInd i acc) val) as [[ctxt2' l2]|]; trivial.
        simpl; move=> [HRel' ->]; split; trivial.
        rewrite context_srel_Union_switch; assumption.
    }
    {
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: move=> elt HIn; apply find_val_imp_find_const; apply HRel; do 3 constructor; assumption.
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: move=> elt HIn; apply find_val_imp_find_const; apply HRel; do 3 constructor; assumption.
        destruct (eval_arith_expr ctxt2 ae1) as [i1|]; simpl; trivial.
        destruct (eval_arith_expr ctxt2 ae2) as [i2|]; simpl; trivial.
        specialize HRec with (ARange i1 i2 acc) type_ctxt ctxt1 ctxt2 val (Union ident s (Union ident (aexpr_freevars ae1) (aexpr_freevars ae2))).
        move: HRec; impl_tac.
        by rewrite context_srel_Union2_comm; rewrite <- context_srel_Union_switch; assumption.
        destruct (bind_aux ctxt1 type_ctxt v (ARange i1 i2 acc) val) as [[ctxt1' l1]|]; trivial.
        destruct (bind_aux ctxt2 type_ctxt v (ARange i1 i2 acc) val) as [[ctxt2' l2]|]; trivial.
        simpl; move=> [HRel' ->]; split; trivial.
        rewrite context_srel_Union_switch; rewrite context_srel_Union2_comm; assumption.
    }
    {
        pose (f1 := fun ae l => l' <- l; x' <- eval_arith_expr ctxt1 ae; Some (x'::l')).
        pose (f2 := fun ae l => l' <- l; x' <- eval_arith_expr ctxt2 ae; Some (x'::l')).
        fold f1; fold f2.
        assert (fold_right f1 (Some nil) aeL = fold_right f2 (Some nil) aeL) as HEq.
        {
            unfold f1, f2; clear HRec f1 f2 acc type_ctxt val.
            induction aeL as [|hd tl HRec]; simpl; trivial.
            rewrite (eval_aexpr_change_ctxt hd ctxt1 ctxt2).
            1: rewrite HRec; clear HRec.
            + reflexivity.
            + move=> elt HIn; apply HRel; simpl. destruct HIn as [elt' []|elt' HIn'].
                - do 2 constructor; assumption.
                - do 3 constructor; assumption.
                - constructor; assumption.
            + move=> elt HIn; apply find_val_imp_find_const; apply HRel; simpl.
                do 3 constructor; assumption.
        }
        rewrite HEq; clear HEq.
        destruct (fold_right f2 (Some nil) aeL) as [iL|]; simpl; trivial.
        clear f1 f2.
        specialize HRec with (ASlice iL acc) type_ctxt ctxt1 ctxt2 val (Union ident (aexprl_freevars aeL) s).
        move: HRec; impl_tac.
        by rewrite <-context_srel_Union_switch; assumption.
        destruct (bind_aux ctxt1 type_ctxt v (ASlice iL acc) val) as [[ctxt1' l1]|]; trivial.
        destruct (bind_aux ctxt2 type_ctxt v (ASlice iL acc) val) as [[ctxt2' l2]|]; trivial.
        simpl; move=> [HRel' ->]; split; trivial.
        rewrite context_srel_Union_switch; assumption.
    }
Qed.

Lemma context_s_rel_bind_aux_list_compl:
    forall varL val ctxt type_ctxt,
        match bind_aux_list ctxt type_ctxt varL val with
            | Some (ctxt', l) => context_srel (Complement ident (varl_freevars varL)) ctxt ctxt'
            | None => True
        end.
Proof.
    move=> varL; induction varL as [|var varL HRec]; simpl.
    {
        move=> [].
        + reflexivity.
        + by trivial.
    }
    {
        move=> val ctxt type_ctxt.
        pose (p := context_s_rel_bind_aux_compl var AAll val ctxt type_ctxt); move:p.
        case (bind_aux ctxt type_ctxt var AAll val); trivial.
        move=> [ctxt' val'] HRel.
        specialize HRec with val' ctxt' type_ctxt.
        destruct (bind_aux_list ctxt' type_ctxt varL val') as [[]|]; trivial.
        transitivity ctxt'; move=> elt HIn.
        + apply HRel; unfold Complement, In; move=> HIn'; destruct HIn.
            constructor 1; unfold In; assumption.
        + apply HRec; unfold Complement, In; move=> HIn'; destruct HIn.
            constructor 2; unfold In; assumption.
    }
Qed.

Lemma dec_in_aexpr_freevars:
    forall ae elt, {In ident (aexpr_freevars ae) elt} + {not (In ident (aexpr_freevars ae) elt)}.
Proof.
    move=> ae elt; induction ae as [|i | op ae1 HRec1 ae2 HRec2]; simpl.
    {
        right; move=> HIn; destruct HIn.
    }
    {
        case_eq (String.eqb i elt); move=> HEq.
        + left; rewrite String.eqb_eq in HEq; destruct HEq; by constructor.
        + right; move=> HEq'; destruct HEq'; rewrite String.eqb_refl in HEq; auto.
    }
    {
        destruct HRec1.
        + left; constructor; assumption.
        + destruct HRec2.
            - left; constructor; assumption.
            - right; move=> HIn; destruct HIn; auto.
    }
Qed.

Lemma dec_in_aexprl_freevars:
    forall aeL elt, {In ident (aexprl_freevars aeL) elt} + {not (In ident (aexprl_freevars aeL) elt)}.
Proof.
    move=> aeL elt; induction aeL as [|hd tl HRec]; simpl.
    {
        right; move=> HIn; destruct HIn.
    }
    {
        destruct HRec.
        + left; constructor; assumption.
        + destruct (dec_in_aexpr_freevars hd elt).
            - left; constructor; assumption.
            - right; move=> HIn; destruct HIn; auto.
    }
Qed.

Lemma dec_in_var_freevars:
    forall var elt, {In ident (var_freevars var) elt} + {not (In ident (var_freevars var) elt)}.
Proof.
    move=> var elt; induction var as [i|v HRec ae|v HRec ae1 ae2|v HRec ael]; simpl.
    {
        case_eq (String.eqb i elt); move=> HEq.
        + left; rewrite String.eqb_eq in HEq; destruct HEq; by constructor.
        + right; move=> HEq'; destruct HEq'; rewrite String.eqb_refl in HEq; auto.
    }
    {
        destruct (dec_in_aexpr_freevars ae elt).
        by left; constructor; assumption.
        destruct HRec.
        by left; constructor; assumption.
        right; move=> HIn; destruct HIn; auto.
    }
    {
        destruct HRec.
        by left; constructor; assumption.
        destruct (dec_in_aexpr_freevars ae1 elt).
        by left; do 2 constructor; assumption.
        destruct (dec_in_aexpr_freevars ae2 elt).
        by left; do 2 constructor; assumption.
        right; move=> HIn; destruct HIn as [|elt' []]; auto.
    }
    {
        destruct HRec.
        by left; constructor; assumption.
        destruct (dec_in_aexprl_freevars ael elt).
        by left; constructor; assumption.
        right; move=> HIn; destruct HIn; auto.
    }
Qed.

Lemma dec_in_varl_freevars:
    forall varL elt, {In ident (varl_freevars varL) elt} + {not (In ident (varl_freevars varL) elt)}.
Proof.
    move=> varL elt; induction varL as [|hd tl HRec]; simpl.
    {
        right; move=> HIn; destruct HIn.
    }
    {
        destruct HRec.
        + left; constructor; assumption.
        + destruct (dec_in_var_freevars hd elt).
            - left; constructor; assumption.
            - right; move=> HIn; destruct HIn; auto.
    }
Qed.

Lemma context_s_rel_bind_aux_list:
    forall varL type_ctxt ctxt1 ctxt2 val s,
    context_srel (Union ident (varl_freevars varL) s) ctxt1 ctxt2 ->
        opt_rel (fun p1 p2 => context_srel (Union ident (varl_freevars varL) s) p1.1 p2.1 /\ p1.2 = p2.2) (bind_aux_list ctxt1 type_ctxt varL val) (bind_aux_list ctxt2 type_ctxt varL val).
Proof.
    move=> varL; induction varL as [|var varL HRec]; simpl.
    {
        move=> _ ctxt1 ctxt2 []; simpl; auto.
    }
    {
        move=> type_ctxt ctxt1 ctxt2 val s HRel.
        pose (p := context_s_rel_bind_aux_compl var AAll val ctxt1 type_ctxt); move:p.
        pose (p := context_s_rel_bind_aux_compl var AAll val ctxt2 type_ctxt); move:p.
        pose (p := context_s_rel_bind_aux var AAll type_ctxt ctxt1 ctxt2 val s); move:p.
        impl_tac.
        {
            move=> elt HIn; apply HRel; destruct HIn.
            + do 2 constructor; assumption.
            + constructor; assumption.
        }
        case (bind_aux ctxt1 type_ctxt var AAll val); simpl.
        2: move=> ->; reflexivity.
        case (bind_aux ctxt2 type_ctxt var AAll val); simpl.
        2: move=> p [].
        move=> [ctxt' val'] [ctxt'2 val'2]; simpl.
        move=> [HRel' ->] HRel2' HRel1'2; clear val'2 val.
        specialize HRec with type_ctxt ctxt'2 ctxt' val' (Union ident (var_freevars var) s); move: HRec.
        impl_tac.
        {
            move=> elt HIn.
            destruct HIn as [elt HIn|elt' []].
            {
                destruct (dec_in_var_freevars var elt).
                + apply HRel'; constructor; assumption.
                + rewrite <- HRel1'2.
                    - rewrite HRel.
                        * apply HRel2'; unfold In, Complement; assumption.
                        * do 2 constructor; assumption.
                    - unfold In, Complement; assumption.
            }
            all: apply HRel'; constructor; assumption.
        }
        destruct (bind_aux_list ctxt'2 type_ctxt varL val') as [[]|]; trivial.
        destruct (bind_aux_list ctxt' type_ctxt varL val') as [[]|]; trivial; simpl.
        rewrite <- context_srel_Union_switch; rewrite context_srel_Union1_comm; auto.
    }
Qed.

Lemma context_srel_bind_compl:
    forall varL val ctxt type_ctxt,
        match bind ctxt type_ctxt varL val with
        | Some ctxt' => context_srel (Complement ident (varl_freevars varL)) ctxt ctxt'
        | None => True
        end.
Proof.
    unfold bind.
    move=> varL val ctxt type_ctxt.
    pose (p := context_s_rel_bind_aux_list_compl varL val ctxt type_ctxt); move:p.
    case (bind_aux_list ctxt type_ctxt varL val); trivial.
    move=> []; simpl; trivial.
    move=> ctxt' []; simpl; trivial.
Qed.

Lemma context_srel_bind:
    forall varL type_ctxt ctxt1 ctxt2 val s,
    context_srel (Union ident (varl_freevars varL) s) ctxt1 ctxt2 ->
        opt_rel (context_srel (Union ident (varl_freevars varL) s)) (bind ctxt1 type_ctxt varL val) (bind ctxt2 type_ctxt varL val).
Proof.
    unfold bind.
    move=> varL type_ctxt ctxt1 ctxt2 val s HRel.
    pose (p := context_s_rel_bind_aux_list varL type_ctxt ctxt1 ctxt2 val s HRel); move:p.
    destruct (bind_aux_list ctxt1 type_ctxt varL val) as [[ctxt1' l1]|]; simpl.
    2: move=> ->; reflexivity.
    destruct (bind_aux_list ctxt2 type_ctxt varL val) as [[ctxt2' l2]|]; simpl.
    2: move=> [].
    move=> [HRel' ->].
    destruct l2; simpl; auto.
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

Ltac eq_match :=
    lazymatch goal with
    | |- match ?A with Some _ => _ | None => _ end = match ?B with Some _ => _ | None => _  end =>
        let H := fresh "H" in
        assert (A = B) as H; [> idtac | rewrite H; reflexivity]
    end.

Ltac small_eq_match :=
    lazymatch goal with
    | |- match ?A with Some _ => _ | None => _ end = match ?B with Some _ => _ | None => _  end =>
        let H := fresh "H" in
        assert (A = B) as H; [> idtac | rewrite H; destruct B]
    end.

Theorem fold_left_equal {A B : Type} :
    forall f1 f2 : A -> B -> A,
        (forall a1 a2, f1 a1 a2 = f2 a1 a2) -> 
        forall (l : list B), forall init : A, fold_left f1 l init = fold_left f2 l init.
Proof.
    move=> f1 f2 HEq l; induction l as [|h l HRec]; simpl; trivial.
    move=> init; rewrite HEq; rewrite HRec; trivial.
Qed.

Theorem eval_var_change_ctxt:
    forall v ctxt1 ctxt2 acc,
        context_srel (var_freevars v) ctxt1 ctxt2 ->
        eval_var ctxt1 v acc = eval_var ctxt2 v acc.
Proof.
    move=> v ctxt1 ctxt2; induction v as [|v HRec ind| v HRec ind1 ind2| v HRec indL]; simpl; move=> acc HRel.
    {
        rewrite HRel.
        2: by constructor.
        destruct (find_val ctxt2 i) as [|]; trivial.
    }
    {
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: move=> x HIn; apply find_val_imp_find_const; apply HRel; constructor; assumption.
        case (eval_arith_expr ctxt2 ind); trivial.
        move=> n; apply HRec.
        move=> elt HIn; apply HRel; constructor; assumption.
    }
    {
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: move=> x HIn; apply find_val_imp_find_const; apply HRel; do 2 constructor; assumption.
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: move=> x HIn; apply find_val_imp_find_const; apply HRel; do 2 constructor; assumption.
        case (eval_arith_expr ctxt2 ind1); trivial.
        case (eval_arith_expr ctxt2 ind2); trivial.
        move=> n1 n2; rewrite HRec; trivial.
        move=> elt HIn; apply HRel.
        constructor; assumption.
    }
    {
        small_eq_match; trivial.
        2: apply HRec; move=> elt HIn; apply HRel; constructor; assumption.
        clear HRec.
        induction indL as [|hd tl HRec]; simpl; trivial.
        small_eq_match; trivial.
        {
            apply HRec.
            move=> elt HIn; apply HRel; simpl; destruct HIn.
            + constructor; assumption.
            + do 2 constructor; assumption.
        }
        {
            eq_match; apply eval_aexpr_change_ctxt.
            move=> elt HIn; apply find_val_imp_find_const.
            apply HRel; do 2 constructor; assumption.
        }
    }
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
    | DLEqn : list var -> expr -> bool -> deqL -> deqL
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
    forall eqns type_ctxt ctxt1 ctxt2 s,
        (forall elt, In ident (deqs_vars (list_deq_of_deqL eqns)) elt -> In ident s elt)
        -> context_srel s ctxt1 ctxt2
        -> opt_rel (context_srel s)
            (eval_deq_list arch prog type_ctxt ctxt1 (list_deq_of_deqL eqns))
            (eval_deq_list arch prog type_ctxt ctxt2 (list_deq_of_deqL eqns)).
Proof.
    move=> eqns; induction eqns as [|v e b tl HRec|i a1 a2 body HRecBody opt tl HRecTL]; simpl; auto.
    {
        move=> type_ctxt ctxt1 ctxt2 s HSubset HRel.
        rewrite (eval_expr_change_ctxt _ _ _ ctxt1 ctxt2).
        2: by move=> x HIn; apply HRel; apply HSubset; do 2 constructor; assumption.
        destruct (eval_expr arch prog ctxt2 e) as [val|].
        2: reflexivity.
        assert (context_srel (Union ident (varl_freevars v) s) ctxt1 ctxt2) as HRel'
        by (move=> x [x' HIn|x' HIn]; apply HRel; trivial; apply HSubset; do 2 constructor; assumption).
        pose (p := context_srel_bind _ type_ctxt _ _ val _ HRel'); move:p; clear HRel'.
        destruct (bind ctxt1 type_ctxt v val) as [ctxt1'|]; destruct (bind ctxt2 type_ctxt v val) as [ctxt2'|]; simpl.
        2: move=> [].
        2: discriminate.
        2: reflexivity.
        move=> HRel'; apply HRec.
        + move=> x HIn; apply HSubset; constructor; assumption.
        + move=> x HIn; apply HRel'; constructor; assumption.
    }
    {
        move=> type_ctxt ctxt1 ctxt2 s HSubset HRel.
        rewrite (eval_aexpr_change_ctxt a1 ctxt1 ctxt2).
        2: move=> x HIn; apply find_val_imp_find_const; apply HRel; apply HSubset; do 3 constructor; assumption.
        rewrite (eval_aexpr_change_ctxt a2 ctxt1 ctxt2).
        2: move=> x HIn; apply find_val_imp_find_const; apply HRel; apply HSubset; do 4 constructor; assumption.
        destruct (eval_arith_expr ctxt2 a1) as [i1|]; simpl; trivial.
        destruct (eval_arith_expr ctxt2 a2) as [i2|]; simpl; trivial.
        assert (opt_rel (context_srel s)
                (loop_rec ctxt1 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2)
                (loop_rec ctxt2 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2))
            as HLoop.
        {
            assert (forall elt, In ident (deqs_vars (list_deq_of_deqL body)) elt -> In ident s elt) as HSubset'
                by (move=> elt HIn; apply HSubset; do 4 constructor; assumption).
            clear HSubset HRecTL a1 a2 tl.
            induction i2 as [|i2 HReci]; simpl; auto.
            case (match i1 with 0 => false | m'.+1 => PeanoNat.Nat.leb i2 m' end); simpl; trivial.
            destruct (loop_rec ctxt1 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt1'|].
            2: simpl in HReci; rewrite HReci; reflexivity.
            destruct (loop_rec ctxt2 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt2'|].
            all: simpl in HReci.
            2: by destruct HReci.
            apply HRecBody; trivial.
            move=> x HIn; simpl.
            case (String.eqb x i); trivial; apply HReci; assumption.
        }
        destruct (loop_rec ctxt1 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt1'|].
        2: simpl in HLoop; rewrite HLoop; reflexivity.
        destruct (loop_rec ctxt2 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt2'|].
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
    forall eqns type_ctxt ctxt,
        match eval_deq_list arch prog type_ctxt ctxt (list_deq_of_deqL eqns) with
        | None => True
        | Some ctxt' => context_srel (Complement ident (deqs_boundvars (list_deq_of_deqL eqns))) ctxt ctxt'
        end.
Proof.
    move=> eqns; induction eqns as [|var e b tl HRecTL| i a1 a2 body HRecBody opt tl HRecTL]; simpl.
    { reflexivity. }
    {
        move=> type_ctxt ctxt.
        destruct (eval_expr arch prog ctxt e) as [val|]; simpl; trivial.
        pose (p := context_srel_bind_compl var val ctxt type_ctxt); move:p.
        destruct (bind ctxt type_ctxt var val) as [ctxt'|]; simpl; trivial.
        specialize HRecTL with type_ctxt ctxt'.
        destruct (eval_deq_list arch prog type_ctxt ctxt' (list_deq_of_deqL tl)) as [ctxt'2|]; trivial.
        move=> HRel; transitivity ctxt'; move=> x HIn.
        + apply HRel; unfold Complement; unfold In; move=> not_var.
            destruct HIn; constructor 1; unfold In; assumption.
        + apply HRecTL; unfold Complement; unfold In; move=> not_var.
            destruct HIn; constructor 2; unfold In; assumption.
    }
    {
        move=> type_ctxt ctxt.
        destruct (eval_arith_expr ctxt a1) as [i1|]; simpl; trivial.
        destruct (eval_arith_expr ctxt a2) as [i2|]; simpl; trivial.
        assert (match loop_rec ctxt ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2 with
            | None => True
            | Some ctxt' => context_srel (Complement ident (Union ident (Singleton ident i) (deqs_boundvars (list_deq_of_deqL body)))) ctxt ctxt'
            end) as HLoop.
        {
            clear HRecTL tl a1 a2; induction i2 as [|i2 HReci]; simpl.
            { reflexivity. }
            case (match i1 with 0 => false | m'.+1 => PeanoNat.Nat.leb i2 m' end).
            { reflexivity. }
            destruct (loop_rec ctxt ((eval_deq_list arch prog type_ctxt)^~(list_deq_of_deqL body)) i i1 i2) as [ctxt'|]; trivial.
            specialize HRecBody with type_ctxt ((i, CoIL i2) :: ctxt').
            destruct (eval_deq_list arch prog type_ctxt ((i, CoIL i2)::ctxt') (list_deq_of_deqL body)) as [ctxt'2|]; trivial.
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
        destruct (loop_rec ctxt ((eval_deq_list arch prog type_ctxt)^~(list_deq_of_deqL body)) i i1 i2) as [ctxt'|]; trivial.
        specialize HRecTL with type_ctxt (match find_val ctxt i with Some v => (i,v)::ctxt' | None=> ctxt' end).
        destruct (find_val ctxt i) as [val|].
        {
            destruct (eval_deq_list arch prog type_ctxt ((i, val)::ctxt') (list_deq_of_deqL tl)) as [ctxt'2|]; trivial.
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
            destruct (eval_deq_list arch prog type_ctxt ctxt' (list_deq_of_deqL tl)) as [ctxt'2|]; trivial.
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
    forall i i1 i2 body ctxt type_ctxt,
        match loop_rec ctxt ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2 with
        | None => True
        | Some ctxt' => context_srel (Complement ident (Union ident (Singleton ident i) (deqs_boundvars (list_deq_of_deqL body)))) ctxt ctxt'
        end.
Proof.
    move=> i i1 i2 body ctxt type_ctxt; induction i2 as [|i2 HRec]; simpl.
    { reflexivity. }
    case (match i1 with 0 => false | m'.+1 => PeanoNat.Nat.leb i2 m' end).
    { reflexivity. }
    destruct (loop_rec ctxt ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt'|]; trivial.
    pose (p := eval_deq_list_unchanged_ctxt arch prog body type_ctxt ((i, CoIL i2)::ctxt')); move:p.
    destruct (eval_deq_list arch prog type_ctxt ((i, CoIL i2)::ctxt') (list_deq_of_deqL body)) as [ctxt'2|]; trivial.
    move=> HBody; transitivity ctxt'; trivial.
    move=> elt HIn; rewrite <- HBody.
    + simpl.
        assert (String.eqb elt i = false) as HEq.
        2: by rewrite HEq; reflexivity.
        rewrite <- not_true_iff_false; rewrite String.eqb_eq; move=> HEq; destruct HEq.
        destruct HIn; do 2 constructor 1.
    + unfold Complement, In; intro; destruct HIn; constructor 2; unfold In; assumption.
Qed.
