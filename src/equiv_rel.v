From Usuba Require Import utils usuba_AST usuba_sem usuba_semProp arch.
Require Import ZArith.
Require Import RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
(* Require Import Bool. *)
Require Import Lia.
Require Import Setoid.
From mathcomp Require Import all_ssreflect.

Section Rel.

Context { arch : architecture}.

Definition expr_rel (e1 e2 : expr) :=
    forall prog ctxt, eval_expr arch prog ctxt e1 = eval_expr arch prog ctxt e2.

Definition expr_rel2 (t1 t2 : (expr * prog_ctxt * context)) :=
    let (p1, ctxt1) := t1 in let (e1, prog1) := p1 in
    let (p2, ctxt2) := t2 in let (e2, prog2) := p2 in
    eval_expr arch prog1 ctxt1 e1 <> None ->
    eval_expr arch prog1 ctxt1 e1 = eval_expr arch prog2 ctxt2 e2.

Definition context_rel (c1 c2 : context) :=
    forall i : ident, find_val c1 i = find_val c2 i.

Definition context_srel (s : Ensemble ident) (c1 c2 : context) :=
    forall i : ident, In ident s i -> find_val c1 i = find_val c2 i.

Definition context_csrel (s : Ensemble ident) (c1 c2 : context) :=
    forall i : ident, In ident s i -> find_const c1 i = find_const c2 i.
            
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

Definition node_sem_rel (n1 n2 : node_sem_type) :=
    forall opt args, n1 opt args <> None -> n1 opt args = n2 opt args.

Definition nodes_rel (n1 n2 : def) :=
    ID n1 = ID n2 /\ forall prog, node_sem_rel (eval_node arch n1 prog) (eval_node arch n2 prog).

Definition prog_ctxt_rel (p1 p2 : prog_ctxt) :=
    forall v, opt_rel node_sem_rel (find_val p1 v) (find_val p2 v).

Inductive prog_rel : prog -> prog -> Prop :=
    | RelEmpty : prog_rel nil nil
    | RelSame : forall n1 n2 p1 p2, (nodes_rel n1 n2) -> prog_rel p1 p2 -> prog_rel (n1::p1) (n2::p2).
        
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
Add Relation expr expr_rel
    reflexivity proved by expr_rel_refl
    symmetry proved by expr_rel_sym
    transitivity proved by expr_rel_trans as expr_rel_def.

Lemma expr_rel2_refl:
    forall x, expr_rel2 x x.
Proof.
    unfold expr_rel2; auto.
    move=> [[] c]; reflexivity.
Qed.

Lemma expr_rel2_trans:
    forall x y z, expr_rel2 x y -> expr_rel2 y z -> expr_rel2 x z.
Proof.
    unfold expr_rel2; auto.
    move=> [[e1 p1] c1] [[e2 p2] c2] [[e3 p3] c3] Eq1 Eq2 NoErr.
    rewrite <- Eq2.
    all: rewrite <- Eq1; trivial.
Qed.

#[global]
Add Relation (expr * prog_ctxt * context) expr_rel2
    reflexivity proved by expr_rel2_refl
    transitivity proved by expr_rel2_trans as expr_rel2_def.

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
Add Relation context context_rel
    reflexivity proved by context_rel_refl
    symmetry proved by context_rel_sym
    transitivity proved by context_rel_trans as context_rel_def.

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
Add Parametric Relation {s : Ensemble ident} : context (context_srel s)
    reflexivity proved by (context_srel_refl s)
    symmetry proved by (context_srel_sym s)
    transitivity proved by (context_srel_trans s) as context_srel_def.

Lemma context_csrel_refl:
    forall s c, context_csrel s c c.
Proof. unfold context_csrel; reflexivity. Qed.

Lemma context_csrel_sym:
    forall s c c', context_csrel s c c' -> context_csrel s c' c.
Proof.
    move=> s c c'; unfold context_csrel.
    move=> HEq i HIn; rewrite HEq; auto.    
Qed.

Lemma context_csrel_trans:
    forall s c1 c2 c3, context_csrel s c1 c2 -> context_csrel s c2 c3 -> context_csrel s c1 c3.
Proof.
    unfold context_csrel.
    move=> s c1 c2 c3 Eq1 Eq2 i HIn; rewrite Eq1; auto.
Qed.

#[global]
Add Parametric Relation {s : Ensemble ident} : context (context_csrel s)
    reflexivity proved by (context_csrel_refl s)
    symmetry proved by (context_csrel_sym s)
    transitivity proved by (context_csrel_trans s) as context_csrel_def.

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
Add Relation deq deq_rel
    reflexivity proved by deq_rel_refl
    symmetry proved by deq_rel_sym
    transitivity proved by deq_rel_trans as deq_rel_def.

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
Add Relation list_deq deqs_rel
    reflexivity proved by deqs_rel_refl
    symmetry proved by deqs_rel_sym
    transitivity proved by deqs_rel_trans as deqs_rel_def.

Lemma node_sem_rel_refl: forall d, node_sem_rel d d.
Proof. unfold node_sem_rel; reflexivity. Qed.

(* Lemma node_sem_rel_sym: forall d1 d2, node_sem_rel d1 d2 -> node_sem_rel d2 d1.
Proof. unfold node_sem_rel; intros; symmetry; auto. Qed. *)

Lemma node_sem_rel_trans: forall d1 d2 d3, node_sem_rel d1 d2 -> node_sem_rel d2 d3 -> node_sem_rel d1 d3.
Proof.
    unfold node_sem_rel; move=> d1 d2 d3 Eq1 Eq2 opt args H.
    rewrite <- Eq2.
    all: rewrite <- Eq1; trivial.
Qed.

#[global]
Add Relation node_sem_type node_sem_rel
    reflexivity proved by node_sem_rel_refl
    (* symmetry proved by node_sem_rel_sym *)
    transitivity proved by node_sem_rel_trans as node_sem_rel_def.

Lemma nodes_rel_refl: forall d, nodes_rel d d.
Proof. unfold nodes_rel; intro; split; reflexivity. Qed.

(* Lemma nodes_rel_sym: forall d1 d2, nodes_rel d1 d2 -> nodes_rel d2 d1.
Proof. unfold nodes_rel; move=> d1 d2 []; split; symmetry; auto. Qed. *)

Lemma nodes_rel_trans: forall d1 d2 d3, nodes_rel d1 d2 -> nodes_rel d2 d3 -> nodes_rel d1 d3.
Proof.
    unfold nodes_rel; move=> d1 d2 d3 [Eq1' Eq1] [Eq2' Eq2].
    split.
    by rewrite Eq1'; exact Eq2'.
    move=> prog.
    rewrite Eq1; trivial.
Qed.

#[global]
Add Relation def nodes_rel
    reflexivity proved by nodes_rel_refl
    (* symmetry proved by nodes_rel_sym *)
    transitivity proved by nodes_rel_trans as nodes_rel_def.

Lemma prog_ctxt_rel_refl: forall d, prog_ctxt_rel d d.
Proof. unfold prog_ctxt_rel; reflexivity. Qed.

(* Lemma prog_ctxt_rel_sym: forall d1 d2, prog_ctxt_rel d1 d2 -> prog_ctxt_rel d2 d1.
Proof. unfold prog_ctxt_rel; intros. symmetry; auto. Qed. *)

Lemma prog_ctxt_rel_trans: forall d1 d2 d3, prog_ctxt_rel d1 d2 -> prog_ctxt_rel d2 d3 -> prog_ctxt_rel d1 d3.
Proof.
    unfold prog_ctxt_rel; move=> d1 d2 d3 Eq1 Eq2 i.
    transitivity (find_val d2 i); trivial.
Qed.

#[global]
Add Relation prog_ctxt prog_ctxt_rel
    reflexivity proved by prog_ctxt_rel_refl
    (* symmetry proved by prog_ctxt_rel_sym *)
    transitivity proved by prog_ctxt_rel_trans as prog_ctxt_rel_def.

Lemma prog_rel_refl:
    forall d, prog_rel d d.
Proof.
    move=> d; induction d; constructor; auto.
    reflexivity.
Qed.
(* 
Lemma prog_rel_sym:
    forall d1 d2, prog_rel d1 d2 -> prog_rel d2 d1.
Proof.
    move=> d1 d2 H; induction H; constructor; auto.
    symmetry; assumption.
Qed. *)

Lemma prog_rel_trans:
    forall d1 d2 d3, prog_rel d1 d2 -> prog_rel d2 d3 -> prog_rel d1 d3.
Proof.
    move=> d1 d2 d3 H1; move: d3.
    induction H1 as [|n1 n2 p1 p2 r1 rtl1 HRec].
    all: move=> d3 H2; inversion H2.
    all: constructor; auto.
    rewrite r1; assumption.
Qed.

#[global]
Add Relation prog prog_rel
    reflexivity proved by prog_rel_refl
    (* symmetry proved by prog_rel_sym *)
    transitivity proved by prog_rel_trans as prog_rel_def.

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

Lemma var_equiv_sym:
    forall v1 v2, var_equiv v1 v2 -> var_equiv v2 v1.
Proof.
    move=> v1 v2 ve; induction ve; constructor; assumption.
Qed.

Lemma var_equiv_trans:
    forall v1 v2 v3, var_equiv v1 v2 -> var_equiv v2 v3 -> var_equiv v1 v3.
Proof.
    move=> v1 v2 v3 ve; move: v3; induction ve.
    all: move=> v3 ve'; inversion ve'; constructor; auto.
Qed.

#[global]
Add Relation var var_equiv
    reflexivity proved by var_equiv_refl
    symmetry proved by var_equiv_sym
    transitivity proved by var_equiv_trans
        as var_equiv_def.

End Rel.

(* First properties on access *)

Fixpoint unfold_access (acc : access) (v : var) : var :=
    match acc with
    | AAll => v
    | ASlice (i::nil) acc_tl => unfold_access acc_tl (Index v (Const_e (Z.of_nat i)))
    | ASlice l acc_tl => unfold_access acc_tl (Slice v (map (fun i => Const_e (Z.of_nat i)) l))
    end.

Lemma unfold_access_var_equiv:
    forall acc v1 v2,
        var_equiv v1 v2 -> var_equiv (unfold_access acc v1) (unfold_access acc v2).
Proof.
    move=> acc; induction acc as [|iL acc HRec]; simpl; trivial.
    move=> v1 v2 v_equiv.
    destruct iL as [|hd iL]; simpl.
    + apply HRec; constructor; assumption.
    + destruct iL; apply HRec; constructor; assumption.
Qed.

#[global]
Add Morphism unfold_access
    with signature (@eq access) ==> var_equiv ==> var_equiv as unfold_access_morph.
Proof.
    exact unfold_access_var_equiv.
Qed.

(* Well type context *)

Inductive valid_type : typ -> Prop :=
    | VTUint : forall d m nb, nb <> 0 -> valid_type (Uint d m nb)
    | VTArray : forall t l, valid_type t -> valid_type (Array t l)
    | VTNat : valid_type Nat.

Definition valid_type_ctxt (type_ctxt : type_ctxt) : Prop :=
    forall var typ, List.In (var, typ) type_ctxt -> valid_type typ.

Fixpoint val_of_type {A : Type} (val : @cst_or_int A) (typ : typ) (form : list nat): Prop :=
    match typ with
    | Nat => match val with
        | CoIL _ => form = nil
        | CoIR _ _ _ => False
        end
    | Uint d (Mint n) nb =>
        match val with
        | CoIL _ => False
        | CoIR _ _ None => False
        | CoIR d' iL (Some form') =>
            form' = (form ++ nb::nil)
            /\ length iL <> 0
            /\ length iL = prod_list (form ++ nb::nil)
            /\ match d with
                | Hslice => DirH n = d'
                | Vslice => DirV n = d'
                | Bslice => DirB = d'
                | _ => False
                end
        end
    | Uint _ Mnat nb => False
    | Uint _ (Mvar _) nb => False
    | Array typ len =>
        match eval_arith_expr nil len with
        | Some len => val_of_type val typ (len::form)
        | None => False
        end
    end.

Definition well_typed_ctxt (type_ctxt : type_ctxt) (ctxt : context) : Prop :=
    forall var val, List.In (var, val) ctxt ->
        exists typ, find_val type_ctxt var = Some typ
            /\ val_of_type val typ nil.

Lemma well_typed_ctxt_imp_find_val:
    forall ctxt type_ctxt var val,
        well_typed_ctxt type_ctxt ctxt ->
        find_val ctxt var = Some val ->
        exists typ, find_val type_ctxt var = Some typ /\ val_of_type val typ nil.
Proof.
    move=> ctxt type_ctxt var val; induction ctxt as [|[var' val'] tl HRec]; simpl.
    by discriminate.
    case_eq (ident_beq var var').
    {
        move=> HEq; apply internal_ident_dec_bl in HEq; destruct HEq.
        move=> well_typed HEq.
        apply well_typed.
        inversion HEq.
        constructor; reflexivity.
    }
    {
        move=> _ well_typed find_hyp; apply HRec; trivial.
        move=> var2 val2 HIn; apply well_typed.
        constructor; assumption.
    }
Qed.

Lemma valid_typed_ctxt_imp_find_val:
    forall type_ctxt var typ,
        valid_type_ctxt type_ctxt ->
        find_val type_ctxt var = Some typ ->
            valid_type typ.
Proof.
    move=> type_ctxt var typ; induction type_ctxt as [|[var' typ'] tl HRec]; simpl.
    by discriminate.
    case_eq (ident_beq var var').
    {
        move=> HEq; apply internal_ident_dec_bl in HEq; destruct HEq.
        move=> valid HEq.
        unfold valid_type_ctxt in valid.
        apply (valid var).
        inversion HEq.
        constructor; reflexivity.
    }
    {
        move=> _ valid find_hyp; apply HRec; trivial.
        move=> var2 val2 HIn; apply (valid var2).
        constructor; assumption.
    }
Qed.

Lemma val_of_type_len {A : Type} :
    forall iL typ d d' form form' l,
        @val_of_type A (CoIR d iL form) typ l
            -> convert_type typ l = Some (d', form') ->
                match form with None => False | Some f => f = form' end
                /\ prod_list form' = length iL.
Proof.
    move=> iL typ; induction typ as [|d m n|typ HRec aelen]; simpl.
    { move=> _ d _ form' _ []. }
    {
        move=> d0 d' form form' l.
        destruct m.
        2-3: by move=> [].
        destruct form.
        2: by move=> [].
        destruct d.
        4-6: by move=> [_ [_ [_ []]]].
        all: move=> [HEq_sf [_ [HEq_prod ->]]] HEq_some; inversion HEq_some.
        all: auto.
    }
    {
        move=> d0 d form form' l.
        destruct (eval_arith_expr nil aelen) as [len|].
        2: by move=> [].
        apply HRec.
    }
Qed.

(* Properties on context_srel and opt_rel *)

Lemma context_srel_Union:
    forall s1 s2 c1 c2,
        context_srel (Union ident s1 s2) c1 c2 <->
            context_srel s1 c1 c2 /\ context_srel s2 c1 c2.
Proof.
    intros; split.
    {
        move=> H; split; move=> elt HIn; apply H.
        all: constructor; assumption.
    }
    move=> [H1 H2] elt [elt' HIn| elt' HIn]; [> apply H1 | apply H2]; assumption.
Qed.

Lemma context_srel_Union_switch:
    forall s1 s2 s3 c1 c2,
        context_srel (Union ident (Union ident s1 s2) s3) c1 c2 <-> 
        context_srel (Union ident s1 (Union ident s2 s3)) c1 c2.
Proof.
    intros.
    repeat rewrite context_srel_Union.
    rewrite and_assoc; split; auto.
Qed.

Lemma context_srel_Union1_comm:
    forall s1 s2 s3 c1 c2,
        context_srel (Union ident (Union ident s1 s2) s3) c1 c2 <-> 
        context_srel (Union ident (Union ident s2 s1) s3) c1 c2.
Proof.
    intros; repeat rewrite context_srel_Union; do 2 rewrite and_assoc.
    split; move=> [H1 [H2 H3]]; auto.
Qed.

Lemma context_srel_Union2_comm:
    forall s1 s2 s3 c1 c2,
        context_srel (Union ident s1 (Union ident s2 s3)) c1 c2 <-> 
        context_srel (Union ident s1 (Union ident s3 s2)) c1 c2.
Proof.
    intros; repeat rewrite context_srel_Union.
    split; move=> [H1 [H2 H3]]; auto.
Qed.

Lemma opt_rel_context_srel_change_set:
    forall s1 s2,
        (forall c1 c2, context_srel s1 c1 c2 <-> context_srel s2 c1 c2) ->
        forall o1 o2, opt_rel (context_srel s1) o1 o2 <-> opt_rel (context_srel s2) o1 o2.
Proof.
    move=> s1 s2 Hypo [c1|] [c2|]; split; simpl; trivial.
    all: rewrite Hypo; trivial.
Qed.

(* Implication of relations *)

Theorem context_srel_imp_context_csrel:
    forall s c1 c2, context_srel s c1 c2 -> context_csrel s c1 c2.
Proof.
    unfold context_csrel, context_srel.
    intros; apply find_val_imp_find_const.
    auto.
Qed.

(* Properties about changing context *)

Lemma eval_aexpr_change_ctxt_lemma:
    (forall e ctxt1 ctxt2,
        (context_csrel (aexpr_freevars e) ctxt1 ctxt2) ->
        eval_arith_expr_inner ctxt1 e = eval_arith_expr_inner ctxt2 e).
Proof.
    move=> e; induction e as [| |op e1 HRec1 e2 HRec2]; simpl; trivial.
    {
        move=> c1 c2 HImpl.
        eq_match.
        apply HImpl; constructor.
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

Theorem eval_aexpr_change_ctxt:
    (forall e ctxt1 ctxt2,
        (context_csrel (aexpr_freevars e) ctxt1 ctxt2) ->
        eval_arith_expr ctxt1 e = eval_arith_expr ctxt2 e).
Proof.
    unfold eval_arith_expr.
    intros; eq_match.
    apply eval_aexpr_change_ctxt_lemma; trivial.
Qed.

#[global]
Add Parametric Morphism (e : arith_expr) : (eval_arith_expr^~ e)
    with signature (context_csrel (aexpr_freevars e)) ==> eq as eval_aexpr_morph.
Proof. apply eval_aexpr_change_ctxt. Qed.

Lemma context_s_rel_bind_aux_compl:
    forall var acc val ctxt type_ctxt b,
        match bind_aux ctxt type_ctxt var acc val b with
            | Some (ctxt', l) => context_srel (Complement ident (var_freevars var)) ctxt ctxt'
            | None => True
        end.
Proof.
    move=> var; induction var as [v|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl.
    all: move=> acc val ctxt type_ctxt b.
    {
        destruct (find_val type_ctxt v) as [typ|]; trivial.
        destruct (convert_type typ nil) as [[dir form]|]; trivial.
        pose (iL := match find_val ctxt v with | Some c => match c with | CoIL i => Some i::nil | CoIR _ iL _ => iL end | None => undefined (prod_list form) end).
        fold iL.
        destruct (update form iL acc val dir) as [[val' e']|]; trivial; clear iL.
        move=> elt HIn; simpl.
        case_eq (ident_beq elt v); trivial.
        move=> HEq; apply internal_ident_dec_bl in HEq; destruct HEq.
        destruct HIn; constructor.
    }
    {
        destruct (eval_arith_expr ctxt ae) as [i|]; trivial.
        specialize HRec with (ASlice [:: i] acc) val ctxt type_ctxt b.
        destruct (bind_aux ctxt type_ctxt v (ASlice [:: i] acc) val) as [[ctxt' _]|]; trivial.
        move=> elt HIn; apply HRec.
        unfold In, Complement; move=> HIn'; destruct HIn.
        constructor; assumption.
    }
    {
        destruct (eval_arith_expr ctxt ae1) as [i1|]; trivial.
        destruct (eval_arith_expr ctxt ae2) as [i2|]; trivial.
        specialize HRec with (ASlice (gen_range i1 i2) acc) val ctxt type_ctxt b.
        destruct (bind_aux ctxt type_ctxt v (ASlice (gen_range i1 i2) acc) val) as [[ctxt' _]|]; trivial.
        move=> elt HIn; apply HRec.
        unfold In, Complement; move=> HIn'; destruct HIn.
        constructor; assumption.
    }
    {
        pose (f := fun ae l => l' <- l; x' <- eval_arith_expr ctxt ae; Some (x'::l')).
        fold f.
        destruct (fold_right f (Some nil) aeL) as [iL|]; trivial; clear f.
        specialize HRec with (ASlice iL acc) val ctxt type_ctxt b.
        destruct (bind_aux ctxt type_ctxt v (ASlice iL acc) val) as [[ctxt' val']|]; trivial.
        move=> elt HIn; apply HRec.
        unfold In, Complement; move=> HIn'; destruct HIn.
        constructor; assumption.
    }
Qed.

Theorem fold_right_equal {A B : Type} :
    forall f1 f2 : A -> B -> B,
        (forall a1 a2, f1 a1 a2 = f2 a1 a2) -> 
        forall (l : list A), forall init : B, fold_right f1 init l = fold_right f2 init l.
Proof.
    move=> f1 f2 HEq l; induction l as [|h l HRec]; simpl; trivial.
    move=> init; rewrite HEq; rewrite HRec; trivial.
Qed.

Lemma context_s_rel_bind_aux:
    forall var acc type_ctxt ctxt1 ctxt2 val s b,
    context_srel (Union ident (var_freevars var) s) ctxt1 ctxt2 ->
        opt_rel (fun p1 p2 => context_srel (Union ident (var_freevars var) s) p1.1 p2.1 /\ p1.2 = p2.2) (bind_aux ctxt1 type_ctxt var acc val b) (bind_aux ctxt2 type_ctxt var acc val b).
Proof.
    move=> var; induction var as [v|v HRec ae|v HRec ae1 ae2|v HRec aeL]; simpl.
    all: move=> acc type_ctxt ctxt1 ctxt2 val s b HRel.
    {
        destruct (find_val type_ctxt v) as [typ|]; simpl; trivial.
        destruct (convert_type typ nil) as [[dir form]|]; simpl; trivial.
        rewrite (HRel v).
        2: by do 2 constructor.
        pose (iL := match find_val ctxt2 v with | Some c => match c with | CoIL i => Some i::nil | CoIR _ iL _ => iL end | None => undefined (prod_list form) end).
        fold iL.
        destruct (update form iL acc val dir) as [[val' e']|]; simpl; trivial; clear iL.
        split; trivial.
        move=> elt HIn; simpl.
        case_eq (ident_beq elt v); trivial.
        move=> HEq; apply HRel; assumption.
    }
    {
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: apply context_srel_imp_context_csrel; move=> elt HIn; apply HRel; do 2 constructor; assumption.
        destruct (eval_arith_expr ctxt2 ae) as [i|]; simpl; trivial.
        specialize HRec with (ASlice [:: i] acc) type_ctxt ctxt1 ctxt2 val (Union ident (aexpr_freevars ae) s) b.
        move: HRec.
        impl_tac.
        by rewrite <- context_srel_Union_switch; assumption.
        destruct (bind_aux ctxt1 type_ctxt v (ASlice [:: i] acc) val) as [[ctxt1' l1]|]; trivial.
        destruct (bind_aux ctxt2 type_ctxt v (ASlice [:: i] acc) val) as [[ctxt2' l2]|]; trivial.
        simpl; move=> [HRel' ->]; split; trivial.
        rewrite context_srel_Union_switch; assumption.
    }
    {
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: apply context_srel_imp_context_csrel; move=> elt HIn; apply HRel; do 3 constructor; assumption.
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: apply context_srel_imp_context_csrel; move=> elt HIn; apply HRel; do 3 constructor; assumption.
        destruct (eval_arith_expr ctxt2 ae1) as [i1|]; simpl; trivial.
        destruct (eval_arith_expr ctxt2 ae2) as [i2|]; simpl; trivial.
        specialize HRec with (ASlice (gen_range i1 i2) acc) type_ctxt ctxt1 ctxt2 val (Union ident s (Union ident (aexpr_freevars ae1) (aexpr_freevars ae2))) b.
        move: HRec; impl_tac.
        by rewrite context_srel_Union2_comm; rewrite <- context_srel_Union_switch; assumption.
        destruct (bind_aux ctxt1 type_ctxt v (ASlice (gen_range i1 i2) acc) val) as [[ctxt1' l1]|]; trivial.
        destruct (bind_aux ctxt2 type_ctxt v (ASlice (gen_range i1 i2) acc) val) as [[ctxt2' l2]|]; trivial.
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
            + apply context_srel_imp_context_csrel; move=> elt HIn; apply HRel; simpl.
                do 3 constructor; assumption.
        }
        rewrite HEq; clear HEq.
        destruct (fold_right f2 (Some nil) aeL) as [iL|]; simpl; trivial.
        clear f1 f2.
        specialize HRec with (ASlice iL acc) type_ctxt ctxt1 ctxt2 val (Union ident (aexprl_freevars aeL) s) b.
        move: HRec; impl_tac.
        by rewrite <-context_srel_Union_switch; assumption.
        destruct (bind_aux ctxt1 type_ctxt v (ASlice iL acc) val) as [[ctxt1' l1]|]; trivial.
        destruct (bind_aux ctxt2 type_ctxt v (ASlice iL acc) val) as [[ctxt2' l2]|]; trivial.
        simpl; move=> [HRel' ->]; split; trivial.
        rewrite context_srel_Union_switch; assumption.
    }
Qed.

Lemma context_s_rel_bind_aux_list_compl:
    forall varL val ctxt type_ctxt b,
        match bind_aux_list ctxt type_ctxt varL val b with
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
        move=> val ctxt type_ctxt b.
        pose (p := context_s_rel_bind_aux_compl var AAll val ctxt type_ctxt b); move:p.
        case (bind_aux ctxt type_ctxt var AAll val b); trivial.
        move=> [ctxt' val'] HRel.
        specialize HRec with val' ctxt' type_ctxt b.
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
        case_eq (ident_beq i elt); move=> HEq.
        + left; apply internal_ident_dec_bl in HEq; destruct HEq; by constructor.
        + right; move=> HEq'; destruct HEq'.
            rewrite internal_ident_dec_lb in HEq; auto.
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
        case_eq (ident_beq i elt); move=> HEq.
        + left; apply internal_ident_dec_bl in HEq; destruct HEq; by constructor.
        + right; move=> HEq'; destruct HEq'.
            rewrite internal_ident_dec_lb in HEq; auto.
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
    forall varL type_ctxt ctxt1 ctxt2 val s b,
    context_srel (Union ident (varl_freevars varL) s) ctxt1 ctxt2 ->
        opt_rel (fun p1 p2 => context_srel (Union ident (varl_freevars varL) s) p1.1 p2.1 /\ p1.2 = p2.2) (bind_aux_list ctxt1 type_ctxt varL val b) (bind_aux_list ctxt2 type_ctxt varL val b).
Proof.
    move=> varL; induction varL as [|var varL HRec]; simpl.
    {
        move=> _ ctxt1 ctxt2 []; simpl; auto.
    }
    {
        move=> type_ctxt ctxt1 ctxt2 val s b HRel.
        pose (p := context_s_rel_bind_aux_compl var AAll val ctxt1 type_ctxt b); move:p.
        pose (p := context_s_rel_bind_aux_compl var AAll val ctxt2 type_ctxt b); move:p.
        pose (p := context_s_rel_bind_aux var AAll type_ctxt ctxt1 ctxt2 val s b); move:p.
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
        specialize HRec with type_ctxt ctxt'2 ctxt' val' (Union ident (var_freevars var) s) b; move: HRec.
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
    forall varL val ctxt type_ctxt b,
        match bind ctxt type_ctxt varL val b with
        | Some ctxt' => context_srel (Complement ident (varl_freevars varL)) ctxt ctxt'
        | None => True
        end.
Proof.
    unfold bind.
    move=> varL val ctxt type_ctxt b.
    pose (p := context_s_rel_bind_aux_list_compl varL val ctxt type_ctxt b); move:p.
    case (bind_aux_list ctxt type_ctxt varL val b); trivial.
    move=> []; simpl; trivial.
    move=> ctxt' []; simpl; trivial.
Qed.

Lemma context_srel_bind:
    forall varL type_ctxt ctxt1 ctxt2 val s b,
    context_srel (Union ident (varl_freevars varL) s) ctxt1 ctxt2 ->
        opt_rel (context_srel (Union ident (varl_freevars varL) s)) (bind ctxt1 type_ctxt varL val b) (bind ctxt2 type_ctxt varL val b).
Proof.
    unfold bind.
    move=> varL type_ctxt ctxt1 ctxt2 val s b HRel.
    pose (p := context_s_rel_bind_aux_list varL type_ctxt ctxt1 ctxt2 val s b HRel); move:p.
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
    move=> i1 i2 i ctxt; induction i2 as [|i2 HRec]; simpl.
    all: destruct PeanoNat.Nat.ltb.
    1,3: by reflexivity.
    {
        move=> elt HIn; simpl.
        case_eq (ident_beq elt i); auto.
        rewrite ident_beq_eq; move=> HEq; destruct HEq.
        destruct HIn; constructor.
    }
    destruct loop_rec; simpl in *.
    2: by discriminate.
    move=> elt HIn; simpl.
    case_eq (ident_beq elt i); auto.
    rewrite ident_beq_eq; move=> HEq; destruct HEq.
    destruct HIn; constructor.
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

Add Parametric Morphism (arch : architecture) : (Eqn)
    with signature (@eq (list var)) ==> (@expr_rel arch) ==> (@eq bool) ==> (@deq_rel arch) as Eqn_morph.
Proof.
    intros; apply expr_rel_IMP_deq_rel; assumption.
Qed.

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
        eval_var v ctxt1 acc = eval_var v ctxt2 acc.
Proof.
    move=> v ctxt1 ctxt2; induction v as [|v HRec ind| v HRec ind1 ind2| v HRec indL]; simpl; move=> acc HRel.
    {
        rewrite HRel.
        2: by constructor.
        destruct (find_val ctxt2 i) as [|]; trivial.
    }
    {
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: apply context_srel_imp_context_csrel; move=> x HIn; apply HRel; constructor; assumption.
        case (eval_arith_expr ctxt2 ind); trivial.
        move=> n; apply HRec.
        move=> elt HIn; apply HRel; constructor; assumption.
    }
    {
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: apply context_srel_imp_context_csrel; move=> x HIn; apply HRel; do 2 constructor; assumption.
        rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
        2: apply context_srel_imp_context_csrel; move=> x HIn; apply HRel; do 2 constructor; assumption.
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
            apply context_srel_imp_context_csrel; move=> elt HIn.
            apply HRel; do 2 constructor; assumption.
        }
    }
Qed.

Add Parametric Morphism (v : var) : (eval_var v)
    with signature (context_srel (var_freevars v)) ==> (@eq access) ==> eq as eval_var_morph.
Proof.
    intros; apply eval_var_change_ctxt; assumption.
Qed.

Theorem find_val_prog_ctxt:
    forall v prog1 prog2,
        prog_ctxt_rel prog1 prog2 ->
        opt_rel node_sem_rel (find_val prog1 v) (find_val prog2 v).
Proof.
    unfold prog_ctxt_rel; auto.
Qed.

Add Morphism find_val
    with signature prog_ctxt_rel ==> eq ==> (opt_rel node_sem_rel) as find_val_prog_morph.
Proof.
    intros; apply find_val_prog_ctxt; trivial.
Qed.

Theorem eval_expr_change_ctxt (arch : architecture):
    forall e ctxt1 ctxt2 prog,
        context_srel (expr_freevars e) ctxt1 ctxt2 ->
        eval_expr arch prog ctxt1 e = eval_expr arch prog ctxt2 e.
Proof.
    move=> e ctxt1 ctxt2 prog.
    move:e ctxt1 ctxt2.
    apply (expr_find
        (fun e => forall ctxt1 ctxt2,
            context_srel (expr_freevars e) ctxt1 ctxt2 ->
            eval_expr arch prog ctxt1 e = eval_expr arch prog ctxt2 e)
        (fun el => forall ctxt1 ctxt2,
            context_srel (exprl_freevars el) ctxt1 ctxt2 ->
            eval_expr_list arch prog ctxt1 el = eval_expr_list arch prog ctxt2 el)); simpl.
    + reflexivity.
    + intros; apply eval_var_change_ctxt. assumption.
    + move=> e' HRec ctxt1 ctxt2 HContent.
        rewrite (HRec ctxt1 ctxt2 HContent); reflexivity.
    + move=> e' HRec ctxt1 ctxt2 HContent.
        rewrite (HRec ctxt1 ctxt2 HContent); trivial.
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
            * apply context_srel_imp_context_csrel; move=> x HIn; apply HContent; constructor; assumption.
        - move=> x HIn; apply HContent; constructor; assumption.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + move=> fname el HRec ctxt1 ctxt2 HContent.
        specialize HRec with ctxt1 ctxt2; move: HRec.
        impl_tac.
        by move=> x HIn; apply HContent; constructor; assumption.
        move=> ->.
        destruct (eval_expr_list arch prog ctxt2 el); trivial.
    + move=> fname ae el HRec ctxt1 ctxt2 HContent.
        specialize HRec with ctxt1 ctxt2; move: HRec.
        impl_tac.
        by move=> x HIn; apply HContent; do 2 constructor; assumption.
        move=> ->.
        destruct (eval_expr_list arch prog ctxt2 el); trivial.
        rewrite (eval_aexpr_change_ctxt ae ctxt1 ctxt2); trivial.
        by apply context_srel_imp_context_csrel; move=> x HIn; apply HContent; do 2 constructor; assumption.
    + reflexivity.
    + move=> e' HRec el HRecL ctxt1 ctxt2 HContent.
        rewrite (HRec ctxt1 ctxt2).
        2: move=> x HIn; apply HContent; constructor; assumption.
        rewrite (HRecL ctxt1 ctxt2); trivial.
        by move => x HIn; apply HContent; constructor; assumption.
Qed.

Theorem eval_expr_change_ctxt2 (arch : architecture):
    (forall e ctxt1 ctxt2 prog1 prog2,
        prog_ctxt_rel prog1 prog2 ->
        context_srel (expr_freevars e) ctxt1 ctxt2 ->
        @expr_rel2 arch (e, prog1, ctxt1) (e, prog2, ctxt2)).
Proof.
    unfold expr_rel2.
    move=> e ctxt1 ctxt2 prog1 prog2 HRelProg.
    move:e ctxt1 ctxt2.
    apply (expr_find
        (fun e => forall ctxt1 ctxt2,
            context_srel (expr_freevars e) ctxt1 ctxt2 ->
            eval_expr arch prog1 ctxt1 e <> None ->
            eval_expr arch prog1 ctxt1 e = eval_expr arch prog2 ctxt2 e)
        (fun el => forall ctxt1 ctxt2,
            context_srel (exprl_freevars el) ctxt1 ctxt2 ->
            eval_expr_list arch prog1 ctxt1 el <> None ->
            eval_expr_list arch prog1 ctxt1 el = eval_expr_list arch prog2 ctxt2 el)); simpl.
    + reflexivity.
    + intros; apply eval_var_change_ctxt. assumption.
    + move=> e' HRec ctxt1 ctxt2 HContent NoErr.
        rewrite (HRec ctxt1 ctxt2 HContent NoErr); reflexivity.
    + move=> e' HRec ctxt1 ctxt2 HContent NoErr.
        rewrite (HRec ctxt1 ctxt2 HContent); trivial.
        move=> H; rewrite H in NoErr; apply NoErr; reflexivity.
    + move=> op e1 HRec1 e2 HRec2 ctxt1 ctxt2 HContent NoErr; rewrite (HRec1 ctxt1 ctxt2).
        - rewrite (HRec2 ctxt1 ctxt2).
            * reflexivity.
            * move=> x HIn; apply HContent; constructor; assumption.
            * move=> H; rewrite H in NoErr.
                destruct (eval_expr _ _ _ e1); apply NoErr; reflexivity.
        - move=> x HIn; apply HContent; constructor; assumption.
        - move=> H; rewrite H in NoErr; apply NoErr; reflexivity.
    + move=> op e1 HRec1 e2 HRec2 ctxt1 ctxt2 HContent NoErr; rewrite (HRec1 ctxt1 ctxt2).
        - rewrite (HRec2 ctxt1 ctxt2).
            * reflexivity.
            * move=> x HIn; apply HContent; constructor; assumption.
            * move=> H; rewrite H in NoErr.
                destruct (eval_expr _ _ _ e1); apply NoErr; reflexivity.
        - move=> x HIn; apply HContent; constructor; assumption.
        - move=> H; rewrite H in NoErr; apply NoErr; reflexivity.
    + move=> op e1 HRec1 a ctxt1 ctxt2 HContent NoErr; rewrite (HRec1 ctxt1 ctxt2).
        - rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
            * reflexivity.
            * apply context_srel_imp_context_csrel; move=> x HIn; apply HContent; constructor; assumption.
        - move=> x HIn; apply HContent; constructor; assumption.
        - move=> H; rewrite H in NoErr; apply NoErr; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + move=> fname el HRec ctxt1 ctxt2 HContent NoErr.
        specialize HRec with ctxt1 ctxt2; move: HRec.
        impl_tac.
        by move=> x HIn; apply HContent; constructor; assumption.
        impl_tac.
        by move=> H; rewrite H in NoErr; apply NoErr; reflexivity.
        move=> HRec; rewrite HRec; rewrite HRec in NoErr; clear HRec.
        destruct (eval_expr_list arch prog2 ctxt2 el); trivial.
        move: NoErr.
        pose (p := HRelProg fname); move: p; clear.
        destruct (find_val prog1 fname) as [n1|]; simpl.
        2: by move=> ->; reflexivity.
        destruct (find_val prog2 fname) as [n2|]; simpl.
        2: by move=> [].
        unfold node_sem_rel.
        move=> rel; specialize rel with None l.
        destruct n1.
        2: move=> H; exfalso; apply H; reflexivity.
        move: rel; impl_tac.
        by discriminate.
        move=> <- _; reflexivity.
    + move=> fname ae el HRec ctxt1 ctxt2 HContent NoErr.
        specialize HRec with ctxt1 ctxt2; move: HRec.
        impl_tac.
        by move=> x HIn; apply HContent; do 2 constructor; assumption.
        impl_tac.
        by move=> H; rewrite H in NoErr; apply NoErr; reflexivity.
        move=> HRec; rewrite HRec; rewrite HRec in NoErr; clear HRec.
        destruct (eval_expr_list arch prog2 ctxt2 el); trivial.
        move: NoErr.
        rewrite (eval_aexpr_change_ctxt ae ctxt1 ctxt2).
        2: by apply context_srel_imp_context_csrel; move=> x HIn; apply HContent; do 2 constructor; assumption.
        destruct (eval_arith_expr ctxt2 ae); trivial.
        pose (p := HRelProg fname); move: p; clear.
        destruct (find_val prog1 fname) as [n1|]; simpl.
        2: by move=> ->; reflexivity.
        destruct (find_val prog2 fname) as [n2|]; simpl.
        2: by move=> [].
        unfold node_sem_rel.
        move=> rel; specialize rel with (Some n) l.
        destruct n1.
        2: move=> H; exfalso; apply H; reflexivity.
        move: rel; impl_tac.
        by discriminate.
        move=> <- _; reflexivity.
    + reflexivity.
    + move=> e' HRec el HRecL ctxt1 ctxt2 HContent NoErr.
        rewrite (HRec ctxt1 ctxt2).
        2: move=> x HIn; apply HContent; constructor; assumption.
        2: move=> H; rewrite H in NoErr; apply NoErr; reflexivity.
        rewrite (HRecL ctxt1 ctxt2); trivial.
        by move => x HIn; apply HContent; constructor; assumption.
        move=> H; rewrite H in NoErr; apply NoErr.
        destruct eval_expr; reflexivity.
Qed.

Lemma loop_rec_equiv:
    forall f1 f2,
        (forall a, f1 a = f2 a) ->
        forall s e init i,
            loop_rec init f1 i s e = loop_rec init f2 i s e.
Proof.
    move=> f1 f2 HEq s e; induction e as [|e HRec]; simpl.
    by move=> init i; rewrite HEq.
    move=> init i.
    destruct PeanoNat.Nat.ltb; trivial.
    rewrite HRec; destruct loop_rec.
    + rewrite HEq; reflexivity.
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

Lemma context_srel_cons:
    forall c1 c2 i s v,
        context_srel s c1 c2 -> context_srel s ((i,v)::c1) ((i,v)::c2).
Proof.
    move=> c1 c2 i s v HRel elt HIn; simpl.
    destruct ident_beq; trivial.
    apply HRel; assumption.
Qed.

Lemma eval_deqL_change_ctxt2 arch:
    forall prog1 prog2,
        prog_ctxt_rel prog1 prog2
        -> forall eqns type_ctxt ctxt1 ctxt2 s,
            (forall elt, In ident (deqs_vars (list_deq_of_deqL eqns)) elt -> In ident s elt)
        -> eval_deq_list arch prog1 type_ctxt ctxt1 (list_deq_of_deqL eqns) <> None
        -> context_srel s ctxt1 ctxt2
        -> opt_rel (context_srel s)
            (eval_deq_list arch prog1 type_ctxt ctxt1 (list_deq_of_deqL eqns))
            (eval_deq_list arch prog2 type_ctxt ctxt2 (list_deq_of_deqL eqns)).
Proof.
    move=> prog1 prog2 HRelProg eqns.
    induction eqns as [|v e b tl HRec|i a1 a2 body HRecBody opt tl HRecTL]; simpl; auto.
    {
        move=> type_ctxt ctxt1 ctxt2 s HSubset NoErr HRel.
        pose (p := eval_expr_change_ctxt2 arch e ctxt1 ctxt2 _ _ HRelProg); unfold expr_rel2 in p.
        move: p; impl_tac.
        by move=> x HIn; apply HRel; apply HSubset; do 2 constructor; assumption.
        impl_tac.
        move=> HEq; rewrite HEq in NoErr; apply NoErr; reflexivity.
        move=> p; rewrite p; rewrite p in NoErr; clear p.
        destruct (eval_expr arch prog2 ctxt2 e) as [val|].
        2: reflexivity.
        assert (context_srel (Union ident (varl_freevars v) s) ctxt1 ctxt2) as HRel'
        by (move=> x [x' HIn|x' HIn]; apply HRel; trivial; apply HSubset; do 2 constructor; assumption).
        pose (p := context_srel_bind _ type_ctxt _ _ val _ b HRel'); move:p; clear HRel'.
        destruct (bind ctxt1 type_ctxt v val) as [ctxt1'|]; destruct (bind ctxt2 type_ctxt v val) as [ctxt2'|]; simpl.
        2: move=> [].
        2: discriminate.
        2: reflexivity.
        move=> HRel'; apply HRec.
        + move=> x HIn; apply HSubset; constructor; assumption.
        + assumption.
        + move=> x HIn; apply HRel'; constructor; assumption.
    }
    {
        move=> type_ctxt ctxt1 ctxt2 s HSubset NoErr HRel.
        move: NoErr.
        rewrite (eval_aexpr_change_ctxt a1 ctxt1 ctxt2).
        2: apply context_srel_imp_context_csrel; move=> x HIn; apply HRel; apply HSubset; do 3 constructor; assumption.
        rewrite (eval_aexpr_change_ctxt a2 ctxt1 ctxt2).
        2: apply context_srel_imp_context_csrel; move=> x HIn; apply HRel; apply HSubset; do 4 constructor; assumption.
        destruct (eval_arith_expr ctxt2 a1) as [i1|]; simpl; trivial.
        destruct (eval_arith_expr ctxt2 a2) as [i2|]; simpl; trivial.
        move=> NoErr.
        assert (opt_rel (context_srel s)
                (loop_rec ctxt1 ((eval_deq_list arch prog1 type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2)
                (loop_rec ctxt2 ((eval_deq_list arch prog2 type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2))
            as HLoop.
        {
            assert (forall elt, In ident (deqs_vars (list_deq_of_deqL body)) elt -> In ident s elt) as HSubset'
                by (move=> elt HIn; apply HSubset; do 4 constructor; assumption).
            assert (loop_rec ctxt1 ((eval_deq_list arch prog1 type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2 <> None) as NoErr'
                by (move=> H; rewrite H in NoErr; apply NoErr; reflexivity).
            clear HSubset HRecTL a1 a2 NoErr tl.
            induction i2 as [|i2 HReci]; simpl in *; auto.
            {
                destruct PeanoNat.Nat.ltb; auto.
                apply HRecBody; auto.
                apply context_srel_cons; assumption.
            }
            destruct PeanoNat.Nat.ltb; simpl in *; trivial.
            destruct (loop_rec ctxt1 ((eval_deq_list arch prog1 type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt1'|].
            2: exfalso; apply NoErr'; reflexivity.
            destruct (loop_rec ctxt2 ((eval_deq_list arch prog2 type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt2'|].
            all: simpl in HReci.
            2: by destruct HReci.
            apply HRecBody; trivial.
            move=> x HIn; simpl.
            case (ident_beq x i); trivial; apply HReci; trivial.
            discriminate.
        }
        destruct (loop_rec ctxt1 ((eval_deq_list arch prog1 type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt1'|].
        2: simpl in HLoop; rewrite HLoop; reflexivity.
        destruct (loop_rec ctxt2 ((eval_deq_list arch prog2 type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt2'|].
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
        by move=> elt HIn; apply HSubset; constructor; assumption.
        by destruct (find_val ctxt1 i). 
        move=> elt HIn.
        case_eq (ident_beq elt i).
        {
            move=> HEq; apply internal_ident_dec_bl in HEq; destruct HEq.
            pose (HEq := HRel elt HIn).
            rewrite HEq.
            case (find_val ctxt2 elt); simpl.
            + rewrite internal_ident_dec_lb; reflexivity.
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

Lemma eval_deqL_change_ctxt arch:
    forall prog,
        forall eqns type_ctxt ctxt1 ctxt2 s,
            (forall elt, In ident (deqs_vars (list_deq_of_deqL eqns)) elt -> In ident s elt)
        -> context_srel s ctxt1 ctxt2
        -> opt_rel (context_srel s)
            (eval_deq_list arch prog type_ctxt ctxt1 (list_deq_of_deqL eqns))
            (eval_deq_list arch prog type_ctxt ctxt2 (list_deq_of_deqL eqns)).
Proof.
    move=> prog eqns.
    induction eqns as [|v e b tl HRec|i a1 a2 body HRecBody opt tl HRecTL]; simpl; auto.
    {
        move=> type_ctxt ctxt1 ctxt2 s HSubset HRel.
        pose (p := eval_expr_change_ctxt arch e ctxt1 ctxt2 prog); unfold expr_rel2 in p.
        move: p; impl_tac.
        by move=> x HIn; apply HRel; apply HSubset; do 2 constructor; assumption.
        move=> ->.
        destruct (eval_expr arch prog ctxt2 e) as [val|].
        2: reflexivity.
        assert (context_srel (Union ident (varl_freevars v) s) ctxt1 ctxt2) as HRel'
        by (move=> x [x' HIn|x' HIn]; apply HRel; trivial; apply HSubset; do 2 constructor; assumption).
        pose (p := context_srel_bind _ type_ctxt _ _ val _ b HRel'); move:p; clear HRel'.
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
        2: apply context_srel_imp_context_csrel; move=> x HIn; apply HRel; apply HSubset; do 3 constructor; assumption.
        rewrite (eval_aexpr_change_ctxt a2 ctxt1 ctxt2).
        2: apply context_srel_imp_context_csrel; move=> x HIn; apply HRel; apply HSubset; do 4 constructor; assumption.
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
            induction i2 as [|i2 HReci]; simpl in *; auto.
            {
                destruct PeanoNat.Nat.ltb; auto.
                apply HRecBody; auto.
                apply context_srel_cons; assumption.
            }
            destruct PeanoNat.Nat.ltb; simpl in *; trivial.
            destruct (loop_rec ctxt1 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt1'|].
            all: destruct (loop_rec ctxt2 ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt2'|].
            all: simpl in HReci.
            2: by destruct HReci.
            2: by discriminate.
            2: by reflexivity.
            apply HRecBody; trivial.
            move=> x HIn; simpl.
            case (ident_beq x i); trivial; apply HReci; trivial.
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
        by move=> elt HIn; apply HSubset; constructor; assumption.
        move=> elt HIn.
        case_eq (ident_beq elt i).
        {
            move=> HEq; apply internal_ident_dec_bl in HEq; destruct HEq.
            pose (HEq := HRel elt HIn).
            rewrite HEq.
            case (find_val ctxt2 elt); simpl.
            + rewrite internal_ident_dec_lb; reflexivity.
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
        pose (p := context_srel_bind_compl var val ctxt type_ctxt b); move:p.
        destruct (bind ctxt type_ctxt var val b) as [ctxt'|]; simpl; trivial.
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
            all: destruct PeanoNat.Nat.ltb; auto.
            1,3: by reflexivity.
            {
                specialize HRecBody with type_ctxt ((i, CoIL 0)::ctxt).
                destruct eval_deq_list; trivial.
                move=> elt HIn; rewrite <- HRecBody.
                {
                    simpl; case_eq (ident_beq elt i); trivial.
                    rewrite ident_beq_eq; move=> HEq; destruct HEq.
                    by destruct HIn; do 2 constructor.
                }
                unfold Complement, In; move=> Abs.
                destruct HIn; constructor 2.
                unfold In; assumption.
            }
            destruct (loop_rec ctxt ((eval_deq_list arch prog type_ctxt)^~(list_deq_of_deqL body)) i i1 i2) as [ctxt'|]; trivial.
            specialize HRecBody with type_ctxt ((i, CoIL i2.+1) :: ctxt').
            destruct eval_deq_list as [ctxt'2|]; trivial.
            transitivity ctxt'; trivial.
            move=> elt HIn; rewrite <- HRecBody.
            + simpl.
                assert (ident_beq elt i = false) as HEq.
                2: by rewrite HEq; reflexivity.
                rewrite <- Bool.not_true_iff_false; move=> HEq; apply internal_ident_dec_bl in HEq; destruct HEq.
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
                assert (ident_beq x i = false) as HEq.
                2: by rewrite HEq; reflexivity.
                rewrite <- Bool.not_true_iff_false; move=> HEq; apply internal_ident_dec_bl in HEq; destruct HEq.
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
    all: destruct PeanoNat.Nat.ltb.
    1,3: by reflexivity.
    {
        pose (p := eval_deq_list_unchanged_ctxt arch prog body type_ctxt ((i, CoIL 0)::ctxt)).
        move:p; move=> p.
        destruct eval_deq_list; trivial.
        move=> elt HIn; rewrite <- p.
        {
            simpl; case_eq (ident_beq elt i); trivial.
            rewrite ident_beq_eq; move=> HEq; destruct HEq.
            by destruct HIn; do 2 constructor.
        }
        unfold Complement, In; move=> Abs.
        destruct HIn; constructor 2.
        unfold In; assumption.
    }
    destruct (loop_rec ctxt ((eval_deq_list arch prog type_ctxt)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt'|]; trivial.
    pose (p := eval_deq_list_unchanged_ctxt arch prog body type_ctxt ((i, CoIL i2.+1)::ctxt')); move:p.
    destruct (eval_deq_list arch prog type_ctxt ((i, CoIL i2.+1)::ctxt') (list_deq_of_deqL body)) as [ctxt'2|]; trivial.
    move=> HBody; transitivity ctxt'; trivial.
    move=> elt HIn; rewrite <- HBody.
    + simpl.
        assert (ident_beq elt i = false) as HEq.
        2: by rewrite HEq; reflexivity.
        rewrite <- Bool.not_true_iff_false; move=> HEq; apply internal_ident_dec_bl in HEq; destruct HEq.
        destruct HIn; do 2 constructor 1.
    + unfold Complement, In; intro; destruct HIn; constructor 2; unfold In; assumption.
Qed.

Fixpoint set_of_list {A : Type} (l : list A) : Ensemble A :=
    match l with
    | nil => Empty_set A
    | hd::tl => Union A (Singleton A hd) (set_of_list tl)
    end.

Theorem extract_ctxt_same:
    forall p c1 c2, context_srel (set_of_list (map VD_ID p)) c1 c2 ->
        extract_ctxt p c1 = extract_ctxt p c2.
Proof.
    move=> p; induction p as [|hd tl HRec]; simpl.
    by reflexivity.
    move=> c1 c2 rel.
    pose (p := rel (VD_ID hd)); move: p.
    impl_tac.
    by do 2 constructor.
    move=> ->.
    rewrite (HRec c1 c2).
    2: by move=> elt Hin; apply rel; constructor.
    reflexivity.
Qed.

Add Parametric Morphism (arch : architecture) : (eval_node arch)
    with signature (@nodes_rel arch) ==> prog_ctxt_rel ==> node_sem_rel as eval_node_morph.
Proof.
    unfold nodes_rel, node_sem_rel.
    move=> x y [IdEq Eq2] p1 p2 prog_rel opt args.
    move=> NoErr.
    specialize Eq2 with p1 opt args; move: Eq2.
    impl_tac; trivial.
    move=> Eq2; move: NoErr; rewrite Eq2.
    clear Eq2 IdEq x.
    destruct y as [i p_in p_out opt' node].
    unfold eval_node.
    destruct node as [tmp deqs| | |l]; simpl; auto.
    all: destruct opt as [index|]; simpl; auto.
    {
        destruct infer_types as [mono_info|].
        2: by move=> H; exfalso; apply H; reflexivity.
        destruct build_ctxt as [ctxt|]; trivial.
        move=> NoErr.
        pose (p := eval_deqL_change_ctxt2 arch _ _ prog_rel
            (deqL_of_list_deq (subst_infer_list_deq mono_info deqs))
            (build_type_ctxt (subst_infer_p mono_info tmp ++
                subst_infer_p mono_info p_in ++ subst_infer_p mono_info p_out))
            ctxt ctxt (Complement ident (Empty_set ident))); move: p.
        impl_tac.
        {
            move=> elt _.
            unfold Complement, In.
            move=> [].
        }
        rewrite deqL_is_list_deq.
        impl_tac.
        {
            destruct eval_deq_list.
            by discriminate.
            auto.
        }
        impl_tac; [> reflexivity | idtac ].
        destruct eval_deq_list; destruct eval_deq_list; simpl.
        2: by move=> [].
        2: by discriminate.
        2: by reflexivity.
        move=> H.
        apply extract_ctxt_same.
        move=> elt HIn; apply H.
        unfold Complement, In.
        move=> [].
    }
    {
        destruct infer_types as [mono_info|].
        2: by move=> H; exfalso; apply H; reflexivity.
        move: l; induction index as [|index Rec].
        all: move=> [|hd tl]; simpl; trivial.
        2: by exact (Rec _).
        destruct hd as [tmp deqs| | |]; simpl; trivial.
        destruct build_ctxt as [ctxt|]; trivial.
        move=> NoErr.
        pose (p := eval_deqL_change_ctxt2 arch _ _ prog_rel
            (deqL_of_list_deq (subst_infer_list_deq mono_info deqs))
            (build_type_ctxt (subst_infer_p mono_info tmp ++
                subst_infer_p mono_info p_in ++ subst_infer_p mono_info p_out))
            ctxt ctxt (Complement ident (Empty_set ident))); move: p.
        impl_tac.
        {
            move=> elt _.
            unfold Complement, In.
            move=> [].
        }
        rewrite deqL_is_list_deq.
        impl_tac.
        {
            destruct eval_deq_list.
            by discriminate.
            auto.
        }
        impl_tac; [> reflexivity | idtac ].
        destruct eval_deq_list; destruct eval_deq_list; simpl.
        2: by move=> [].
        2: by discriminate.
        2: by reflexivity.
        move=> H.
        apply extract_ctxt_same.
        move=> elt HIn; apply H.
        unfold Complement, In.
        move=> [].
    }
Qed.

Add Parametric Morphism (arch : architecture) : (eval_prog arch)
    with signature (@prog_rel arch) ==> prog_ctxt_rel as eval_prog_morph.
Proof.
    move=> x y H; induction H as [|n1 n2 p1 p2 rel_n rel_tl HRec].
    by reflexivity.
    simpl.
    unfold nodes_rel in rel_n.
    destruct rel_n as [HEq rel_n].
    rewrite HEq.
    unfold prog_ctxt_rel; move=> v; simpl.
    case (ident_beq v (ID n2)); simpl; auto.
    rewrite rel_n.
    rewrite HRec; reflexivity.
Qed.

Theorem rewrite_nodes (arch : architecture)(f : def -> def):
    (forall node, @nodes_rel arch node (f node)) ->
    forall prog, @prog_rel arch prog (map f prog).
Proof.
    move=> Hyp; move=> p; induction p as [|node tl HRec].
    all: simpl; constructor; auto.
Qed.
