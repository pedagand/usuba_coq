From Usuba Require Import usuba_AST usuba_sem equiv_rel.
From Coq Require Import MSets MSets.MSetToFiniteSet MSets.MSetFacts.
Require Import Coq.Structures.OrdersEx.

Module iset := Make String_as_OT.

Fixpoint collect_aexpr (e : arith_expr) : iset.t :=
    match e with
    | Var_e i => iset.singleton i
    | Const_e _ => iset.empty
    | Op_e _ e1 e2 => iset.union (collect_aexpr e1) (collect_aexpr e2)
    end.

Fixpoint collect_aexprl (e : list arith_expr) : iset.t :=
    match e with
    | nil => iset.empty
    | h :: tl => iset.union (collect_aexpr h) (collect_aexprl tl)
    end.

Function collect_var (v : var) : iset.t :=
    match v with
    | Var var => iset.singleton var
    | Index v i => iset.union (collect_var v) (collect_aexpr i)
    | Range v s e => iset.union (collect_var v) (iset.union (collect_aexpr s) (collect_aexpr e))
    | Slice v el => iset.union (collect_var v) (collect_aexprl el)
    | VTuple vl => collect_varl vl
    end
with collect_varl vl :=
    match vl with
    | LVnil => iset.empty
    | LVcons v tl => iset.union (collect_var v) (collect_varl tl)
    end.

Function collect_expr (e : expr) : iset.t :=
    match e with
    | Const _ _ => iset.empty
    | ExpVar v => collect_var v
    | Tuple el => collect_exprl el
    | Not e => collect_expr e
    | Log _ e1 e2 | Arith _ e1 e2 => iset.union (collect_expr e1) (collect_expr e2)
    | Shift _ expr aexpr => iset.union (collect_expr expr) (collect_aexpr aexpr)
    | Shuffle v _ => collect_var v
    | Bitmask expr aexpr => iset.union (collect_expr expr) (collect_aexpr aexpr)
    | Pack e1 e2 _ => iset.union (collect_expr e1) (collect_expr e2)
    | Fun f exprl => iset.union (iset.singleton f) (collect_exprl exprl)
    | Fun_v f aexpr exprl => iset.union (iset.singleton f) (iset.union (collect_aexpr aexpr) (collect_exprl exprl))
    end
with collect_exprl el :=
    match el with
    | Enil => iset.empty
    | ECons e el => iset.union (collect_expr e) (collect_exprl el)
    end.

Function collect_vdecl (p : p) : iset.t :=
    match p with
    | nil => iset.empty
    | v :: tl => iset.add (VD_ID v) (collect_vdecl tl)
    end.

Function collect_deq (d : deq) : iset.t :=
    match d with
    | Eqn v e _ => iset.union (collect_var v) (collect_expr e)
    | Loop i aei1 aei2 eqns opt =>
        iset.add i (iset.union 
            (iset.union (collect_aexpr aei1) (collect_aexpr aei2)) (collect_deqs eqns))
    end
with collect_deqs (dl : list_deq) : iset.t :=
    match dl with
    | Dnil => iset.empty
    | Dcons hd tl => iset.union (collect_deq hd) (collect_deqs tl)
    end.

Function collect_bounddeq (d : deq) : iset.t :=
    match d with
    | Eqn v e _ => (collect_var v)
    | Loop i aei1 aei2 eqns opt =>
        iset.add i (collect_bounddeqs eqns)
    end
with collect_bounddeqs (dl : list_deq) : iset.t :=
    match dl with
    | Dnil => iset.empty
    | Dcons hd tl => iset.union (collect_bounddeq hd) (collect_bounddeqs tl)
    end.

Function clean_in_deqs (vars : iset.t) (dL : list_deq) : iset.t * list_deq :=
    match dL with
    | Dcons (Eqn v e l) tl =>
        let (vars', tl) := clean_in_deqs vars tl in 
        let bound_vars := collect_var v in
        if iset.exists_ (fun i => iset.mem i vars') bound_vars
        then (iset.union vars' (iset.union (collect_var v) (collect_expr e)), Dcons (Eqn v e l) tl)
        else (vars', tl)
    | Dcons (Loop i ae1 ae2 body opt) tl =>
        let (vars', tl') := clean_in_deqs vars tl in
        let bounds := collect_bounddeqs body in
        if iset.exists_ (fun elt => iset.mem elt vars') bounds || iset.mem i vars'
        then (iset.add i (iset.union vars' (iset.union (iset.union (collect_aexpr ae1) (collect_aexpr ae2)) (collect_deqs body))), Dcons (Loop i ae1 ae2 body opt) tl')
        else (vars', tl')
    | Dnil => (vars, Dnil)
    end.

Definition clean_node (node : def) : def :=
    match NODE node with
    | Single p eqns =>
        {|
            NODE := Single p (snd (clean_in_deqs (collect_vdecl (P_OUT node)) eqns));
            ID := ID node;
            P_IN := P_IN node;
            P_OUT := P_OUT node;
            OPT := OPT node
        |}
    | _ => node
    end.

From mathcomp Require Import all_ssreflect.
Require Import Coq.Sets.Ensembles.

Lemma iset_empty_soudness:
    forall elt : iset.elt,
    iset.In elt iset.empty <-> In ident (Empty_set ident) elt.
Proof.
    move=> elt.
        pose (Hempty := iset.empty_spec).
        unfold iset.Empty in Hempty.
        specialize Hempty with elt.
        split.
        + move=> H; exfalso; auto.
        + move=> [].
Qed.

Lemma collect_aexpr_soundness:
    forall ae elt,
        iset.In elt (collect_aexpr ae) <-> In ident (aexpr_freevars ae) elt.
Proof.
    move=> ae; induction ae as [| |op ae1 HRec1 ae2 HRec2]; simpl.
    {
        exact iset_empty_soudness.
    }
    {
        move=> elt; rewrite iset.singleton_spec; split.
        + move=> ->; constructor.
        + move=> []; reflexivity.
    }
    {
        move=> elt; rewrite iset.union_spec.
        rewrite HRec1; rewrite HRec2; split.
        + move=> []; constructor; assumption.
        + move=> []; auto.
    }
Qed.

Lemma collect_aexprl_soundness:
    forall ael elt,
        iset.In elt (collect_aexprl ael) <-> In ident (aexprl_freevars ael) elt.
Proof.
    move=> ael; induction ael as [|hd tl HRec]; simpl; move=> elt.
    {
        exact (iset_empty_soudness _).
    }
    {
        rewrite iset.union_spec.
        rewrite collect_aexpr_soundness; rewrite HRec.
        split; move=> []; auto; move=> HIn; constructor; assumption.
    }
Qed.

Lemma collect_var_soundness:
    forall var elt,
        iset.In elt (collect_var var) <-> In ident (var_freevars var) elt.
Proof.
    move=> var.
    eapply (var_find (fun var => forall elt, iset.In elt (collect_var var) <-> In ident (var_freevars var) elt)
        (fun varL => forall elt, iset.In elt (collect_varl varL) <-> In ident (varl_freevars varL) elt) _ _ _ _ _ _ _ var).
    Unshelve.
    all: simpl; auto.
    {
        move=> i elt; rewrite iset.singleton_spec; split.
        + move=> ->; constructor.
        + move=> []; reflexivity.
    }
    {
        move=> v HRec ae elt.
        rewrite iset.union_spec; rewrite HRec; rewrite collect_aexpr_soundness; split.
        + move=> []; constructor; assumption.
        + move=> []; auto.
    }
    {
        move=> v HRec ae1 ae2 elt.
        do 2 rewrite iset.union_spec; rewrite HRec; do 2 rewrite collect_aexpr_soundness; split.
        + move => [|[]].
            - constructor; assumption.
            - do 2 constructor; assumption.
            - do 2 constructor; assumption.
        + move => [|x []]; auto.
    }
    {
        move=> v HRec aeL elt.
        rewrite iset.union_spec; rewrite HRec; rewrite collect_aexprl_soundness; split.
        + move=> []; constructor; assumption.
        + move=> []; auto.
    }
    {
        move=> elt.
        pose (Hempty := iset.empty_spec).
        unfold iset.Empty in Hempty.
        specialize Hempty with elt.
        split.
        + move=> H; exfalso; auto.
        + move=> [].
    }
    {
        move=> v HRec vL HRecL elt.
        rewrite iset.union_spec; rewrite HRec; rewrite HRecL; split.
        + move=> []; constructor; assumption.
        + move=> []; auto.
    }
Qed.

Lemma collect_expr_soundness:
    forall e elt,
        iset.In elt (collect_expr e) <-> In ident (expr_freevars e) elt.
Proof.
    move=> e.
    refine (expr_find (fun e => _) (fun exprL => _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ e); simpl; auto; clear e.
    {
        intros; exact (iset_empty_soudness _).
    }
    {
        intros; exact (collect_var_soundness _ _).
    }
    {
        move=> e0 HRec elt; exact (HRec elt).
    }
    {
        move=> _ e1 HRec1 e2 HRec2 elt.
        rewrite iset.union_spec; rewrite HRec1; rewrite HRec2.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        move=> _ e1 HRec1 e2 HRec2 elt.
        rewrite iset.union_spec; rewrite HRec1; rewrite HRec2.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        move=> _ e1 HRec1 ae elt.
        rewrite iset.union_spec; rewrite HRec1; rewrite collect_aexpr_soundness.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        intros; exact (collect_var_soundness _ _).
    }
    {
        move=> e HRec ae elt; rewrite iset.union_spec.
        rewrite HRec; rewrite collect_aexpr_soundness.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        move=> e1 HRec1 e2 HRec2 typ elt.
        rewrite iset.union_spec; rewrite HRec1; rewrite HRec2.
        split; move=> []; auto; intro; constructor; assumption.
    }
    {
        move=> i el HRec elt; rewrite iset.union_spec.
        rewrite iset.singleton_spec; rewrite HRec.
        split; move=> []; auto.
        + move=> ->; do 2 constructor.
        + intro; constructor; assumption.
        + move=> x []; left; reflexivity.
    }
    {
        move=> i ae el HRec elt; do 2 rewrite iset.union_spec.
        rewrite iset.singleton_spec; rewrite collect_aexpr_soundness; rewrite HRec.
        split.
        + move=> [->|[HIn|HIn]]; do 2 constructor; assumption.
        + move=> [x []| x []]; auto.
    }
    {
        simpl; exact iset_empty_soudness.
    }
    {
        move=> e HRec el HRecl elt; simpl.
        rewrite iset.union_spec; rewrite HRec; rewrite HRecl.
        split; move=> []; auto; intro; constructor; assumption.
    }
Qed.

Lemma collect_deqs_soundness_lemma:
    forall deqs elt,
        iset.In elt (collect_deqs (list_deq_of_deqL deqs)) <-> In ident (deqs_vars (list_deq_of_deqL deqs)) elt.
Proof.
    move=> deqs elt; induction deqs as [|v e b tl HRec|i ae1 ae2 body HRecBody opt tl HRecTL]; simpl.
    {
        exact (iset_empty_soudness _).
    }
    {
        do 2 rewrite iset.union_spec; rewrite HRec.
        rewrite collect_var_soundness; rewrite collect_expr_soundness.
        split; move=> []; auto.
        + move=> []; do 2 constructor; assumption.
        + intro; constructor; assumption.
        + move=> x []; auto.
    }
    {
        rewrite iset.union_spec.
        rewrite iset.add_spec; do 2 rewrite iset.union_spec.
        rewrite HRecBody; rewrite HRecTL.
        do 2 rewrite collect_aexpr_soundness; split.
        + move=> [[|[[]|]]|].
            - by move=> ->; do 3 constructor.
            - intro; do 3 constructor; assumption.
            - intro; do 4 constructor; assumption.
            - intro; do 4 constructor; assumption.
            - intro; do 1 constructor; assumption.
        + move=> [x [x' []|x' [|x'2 []]]|]; auto.
    }
Qed.

Lemma collect_bounddeqs_soundness_lemma:
    forall deqs elt,
        iset.In elt (collect_bounddeqs (list_deq_of_deqL deqs)) <-> In ident (deqs_boundvars (list_deq_of_deqL deqs)) elt.
Proof.
    move=> deqs elt; induction deqs as [|v e b tl HRec|i ae1 ae2 body HRecBody opt tl HRecTL]; simpl.
    {
        exact (iset_empty_soudness _).
    }
    {
        rewrite iset.union_spec; rewrite HRec.
        rewrite collect_var_soundness.
        split; move=> []; auto.
        all: intro; constructor; assumption.
    }
    {
        rewrite iset.union_spec.
        rewrite iset.add_spec.
        rewrite HRecBody; rewrite HRecTL; split.
        + move=> [[]|].
            - by move=> ->; do 2 constructor.
            - intro; do 2 constructor; assumption.
            - intro; do 1 constructor; assumption.
        + move=> [x [x' []|]|]; auto.
    }
Qed.

Lemma collect_deqs_soundness:
    forall deqs elt,
        iset.In elt (collect_deqs deqs) <-> In ident (deqs_vars deqs) elt.
Proof.
    move=> deqs elt.
    pose (HEq := collect_deqs_soundness_lemma (deqL_of_list_deq deqs) elt); move: HEq.
    rewrite deqL_is_list_deq; auto.
Qed.

Lemma clean_in_deqs_freevars:
    forall eqns vars x,
        iset.mem x (fst (clean_in_deqs vars (list_deq_of_deqL eqns))) = true <->
            iset.mem x vars = true \/
            In ident (deqs_vars (snd (clean_in_deqs vars (list_deq_of_deqL eqns)))) x.
Proof.
    move=> eqns; induction eqns as [|v e l tl HRec | i ae1 ae2 dL' HRec1 opt tl HRec2]; simpl.
    {
        split; auto.
        move => [|[]]; trivial.
    }
    {
        move=> vars x; specialize HRec with vars x.
        destruct (clean_in_deqs vars (list_deq_of_deqL tl)); simpl in *.
        case (iset.exists_ (iset.mem^~ t) (collect_var v)); simpl; trivial.
        do 2 rewrite iset.mem_spec; do 2 rewrite iset.mem_spec in HRec.
        do 2 rewrite iset.union_spec; rewrite collect_expr_soundness.
        rewrite collect_var_soundness.
        rewrite HRec; clear HRec; split.
        + move=> [[]|[]]; auto; move=> H; right.
            + constructor; assumption.
            + do 2 constructor; assumption.
            + do 2 constructor; assumption.
        + move=> [HIn|[elt' [elt HIn|elt HIn]|HIn]]; auto.
    }
    {
        move=> vars x; specialize HRec2 with vars x.
        destruct (clean_in_deqs vars (list_deq_of_deqL tl)) as [vars' tl']; simpl in *.
        case (iset.exists_ (iset.mem^~ vars') (collect_bounddeqs (list_deq_of_deqL dL')) || iset.mem i vars'); simpl; auto.
        rewrite iset.mem_spec; rewrite iset.add_spec; do 3 rewrite iset.union_spec; do 2 rewrite collect_aexpr_soundness.
        rewrite collect_deqs_soundness.
        rewrite iset.mem_spec in HRec2; rewrite HRec2; split.
        - move=> [|[[]|[[]|]]]; auto.
            * move=> ->; by do 3 constructor.
            * intros; right; constructor; assumption.
            * intros; right; do 3 constructor; assumption.
            * intros; right; do 4 constructor; assumption.
            * intros; right; do 4 constructor; assumption.
        - move=> [|[elt' [elt []|elt [|elt'2 []]]|]]; auto.
    }
Qed.

Lemma loop_rec_change_ctxt arch prog:
    forall e s body i ens ctxt1 ctxt2,
        context_srel (Union ident (fun elt => iset.In elt (collect_deqs (list_deq_of_deqL body))) ens) ctxt1 ctxt2 ->
        opt_rel (context_srel (Union ident (fun elt => iset.In elt (collect_deqs (list_deq_of_deqL body))) ens))
            (loop_rec ctxt1 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i s e)
            (loop_rec ctxt2 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i s e).
Proof.
    move=> e; induction e as [|e HRec]; simpl; auto.
    move=> s body i ens ctxt1 ctxt2 HRel.
    case (match s with 0 => false | m'.+1 => PeanoNat.Nat.leb e m' end); simpl; auto.
    pose (p := HRec s body i ens ctxt1 ctxt2 HRel); move:p.
    destruct (loop_rec ctxt1 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i s e).
    all: destruct (loop_rec ctxt2 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i s e); simpl; auto.
    2: move=> [].
    2: discriminate.
    move=> HRel2.
    apply eval_deqL_change_ctxt.
    {
        move=> elt HIn.
        constructor 1.
        unfold In.
        rewrite collect_deqs_soundness.
        assumption.
    }
    {
        move=> elt HIn; simpl.
        case (String.eqb elt i); trivial.
        apply HRel2; assumption.
    }
Qed.

Lemma clean_in_deqs_soundness arch prog:
    forall eqns vars ctxt1 ctxt2,
        eval_deq_list arch prog ctxt1 (list_deq_of_deqL eqns) <> None ->
        context_srel (deqs_vars (snd (clean_in_deqs vars (list_deq_of_deqL eqns)))) ctxt1 ctxt2 ->
        context_srel (fun i => iset.mem i vars = true) ctxt1 ctxt2 ->
        opt_rel (context_srel (fun i => iset.mem i vars = true)) (eval_deq_list arch prog ctxt1 (list_deq_of_deqL eqns))
            (eval_deq_list arch prog ctxt2 (snd (clean_in_deqs vars (list_deq_of_deqL eqns)))).
Proof.
    move=> eqns; induction eqns as [|v expr b tl HRec'|i aei1 aei2 body HRecBody opt tl HRecTL]; simpl.
    { auto. }
    {
        move=> vars ctxt1 ctxt2.
        pose (p := clean_in_deqs_freevars tl vars); move:p.
        pose (HRec := HRec' vars); move: HRec.
        destruct (clean_in_deqs vars (list_deq_of_deqL tl)) as [vars' tl']; simpl in *.
        clear HRec'.
        case_eq (iset.exists_ (iset.mem^~ vars') (collect_var v)); simpl.
        {
            move=> _ HRec _ HnoErr HRel1 HRel2.
            rewrite <- (eval_expr_change_ctxt _ _ _ ctxt1 ctxt2).
            + destruct (eval_expr arch prog ctxt1 expr) as [val|]; simpl; trivial.
                assert (context_srel (Union ident (var_freevars v)
                    (Union ident (deqs_vars tl') (fun i : ident => iset.mem i vars = true))) ctxt1 ctxt2) as HRel3.
                {
                    move=> x HIn; destruct HIn as [|x []].
                    + apply HRel1; do 2 constructor; assumption.
                    + apply HRel1; constructor; assumption.
                    + apply HRel2; assumption.
                }
                pose (H := context_srel_bind v _ _ val _ HRel3); move: H.
                destruct (bind ctxt1 v val) as [ctxt1'|]; simpl.
                2: by move=> ->; simpl; reflexivity.
                destruct (bind ctxt2 v val) as [ctxt2'|]; simpl.
                2: by move=> [].
                move=> HRel4; apply HRec; trivial.
                + move=> x HIn; apply HRel4; do 2 constructor; assumption.
                + move=> x HIn; apply HRel4; do 2 constructor; assumption.
            + move=> x HIn; apply HRel1; do 2 constructor; assumption.
        }
        {
            rewrite <- not_true_iff_false.
            rewrite iset.exists_spec.
            move=> NegExists HRec Hfreevars HnoErr HRel1 HRel2.
            case (eval_expr arch prog ctxt1 expr) as [x|].
            2: exfalso; apply HnoErr; reflexivity.
            pose (p := context_srel_bind_compl v x ctxt1); move:p.
            case (bind ctxt1 v x) as [ctxt'|].
            2: exfalso; apply HnoErr; reflexivity.
            move=> HRel3; apply HRec; trivial.
            all: transitivity ctxt1; trivial.
            all: symmetry; move=> elt HIn; apply HRel3.
            all: assert (iset.mem elt vars' = true) as Hfreevars' by (rewrite Hfreevars; auto).
            all: clear Hfreevars; unfold Complement; unfold In; move=> HIn'.
            all: apply NegExists; unfold iset.Exists; exists elt; split; trivial.
            all: rewrite collect_var_soundness; unfold In; assumption.
        }
    }
    {
        move=> vars ctxt1 ctxt2 HnoErr HRel1 HRel2.
        pose (p := clean_in_deqs_freevars tl vars); move:p.
        pose (p := HRecTL vars); move: p; clear HRecTL.
        destruct (clean_in_deqs vars (list_deq_of_deqL tl)) as [vars' tl']; simpl.
        move=> HRecTL.
        case_eq (iset.exists_ (iset.mem^~ vars') (collect_bounddeqs (list_deq_of_deqL body))
            || iset.mem i vars').
        all: move=> HEq; rewrite HEq in HRel1; simpl.
        {
            move=> _; clear HEq; move: HnoErr.
            rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
            2: move=> x HIn; apply find_val_imp_find_const; apply HRel1; simpl; do 3 constructor; assumption.
            rewrite (eval_aexpr_change_ctxt _ ctxt1 ctxt2).
            2: move=> x HIn; apply find_val_imp_find_const; apply HRel1; simpl; do 4 constructor; assumption.
            destruct (eval_arith_expr ctxt2 aei1) as [s|]; simpl; trivial.
            destruct (eval_arith_expr ctxt2 aei2) as [e|]; simpl; trivial.
            assert (context_srel (Union ident (iset.In^~ (collect_deqs (list_deq_of_deqL body)))
               (Union ident (fun i : ident => iset.mem i vars = true) (deqs_vars tl'))) ctxt1 ctxt2) as HRel3.
            {
                move=> x' [x HIn|x'' [x HIn|x HIn]].
                + apply HRel1; simpl; unfold In in HIn; rewrite collect_deqs_soundness in HIn.
                    do 4 constructor; assumption.
                + apply HRel2; assumption.
                + apply HRel1; simpl; constructor; assumption. 
            }
            pose (p := loop_rec_change_ctxt arch prog e s body i _ ctxt1 ctxt2 HRel3); move: p; clear HRel3.
            destruct (loop_rec ctxt1 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i s e) as [ctxt1'|].
            2: move=> _ HnoErr; exfalso; apply HnoErr; reflexivity.
            destruct (loop_rec ctxt2 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i s e) as [ctxt2'|]; simpl.
            2: move=> [].
            assert (match find_val ctxt1 i with Some v => Some ((i, v) :: ctxt1') | None => Some ctxt1' end
                = Some match find_val ctxt1 i with Some v => (i, v)::ctxt1' | None => ctxt1' end) as HEq
                by (case (find_val ctxt1 i); simpl; auto).
            rewrite HEq; clear HEq.
            assert (match find_val ctxt2 i with Some v => Some ((i, v) :: ctxt2') | None => Some ctxt2' end
                = Some match find_val ctxt2 i with Some v => (i, v)::ctxt2' | None => ctxt2' end) as HEq
                by (case (find_val ctxt2 i); simpl; auto).
            rewrite HEq; clear HEq.
            move=> HRel3 HnoErr.
            apply HRecTL; auto; move=> x HIn; case_eq (String.eqb x i).
            1,3: rewrite String.eqb_eq; move=> HEq; destruct HEq.
            {
                assert (find_val ctxt1 x = find_val ctxt2 x) as HEq
                    by (apply HRel1; simpl; constructor; assumption); destruct HEq.
                case (find_val ctxt1 x); simpl.
                + rewrite String.eqb_refl; reflexivity.
                + apply HRel3; do 2 constructor; assumption.
            }
            {
                assert (find_val ctxt1 x = find_val ctxt2 x) as HEq
                    by (apply HRel2; simpl; assumption); destruct HEq.
                case (find_val ctxt1 x); simpl.
                + rewrite String.eqb_refl; reflexivity.
                + apply HRel3; do 2 constructor; assumption.
            }
            all: case (find_val ctxt1 i); case (find_val ctxt2 i); simpl.
            1,5: move=> v v' ->.
            3,4,6,7: move=> v ->.
            7,8: move=> _.
            all: apply HRel3; do 2 constructor; assumption.
        }
        {
            rewrite orb_false_iff in HEq; destruct HEq as [Hexists HnegMem].
            destruct (eval_arith_expr ctxt1 aei1) as [i1|].
            2: exfalso; apply HnoErr; reflexivity.
            destruct (eval_arith_expr ctxt1 aei2) as [i2|].
            2: exfalso; apply HnoErr; reflexivity.
            pose (p := loop_rec_unchanged_ctxt arch prog i i1 i2 body ctxt1); move:p.
            destruct (loop_rec ctxt1 ((eval_deq_list arch prog)^~ (list_deq_of_deqL body)) i i1 i2) as [ctxt'|].
            2: exfalso; apply HnoErr; reflexivity.
            clear HRecBody.
            move=> HRel Hvars'.
            case_eq (find_val ctxt1 i).
            1: move=> v Hfind_val; rewrite Hfind_val in HnoErr.
            2: move=> Hfind_val; rewrite Hfind_val in HnoErr.
            all: apply HRecTL; trivial; transitivity ctxt1; trivial; symmetry.
            all: move=> elt HIn; simpl.
            {
                case_eq (String.eqb elt i).
                + rewrite String.eqb_eq; move=> HEq2; destruct HEq2; assumption.
                + move=> HnotEq; apply HRel; unfold Complement, In; move=> HIn'.
                    rewrite <- not_true_iff_false in Hexists; apply Hexists.
                    rewrite iset.exists_spec; unfold iset.Exists.
                    exists elt.
                    destruct HIn' as [elt' []|].
                    by rewrite String.eqb_refl in HnotEq.
                    rewrite collect_bounddeqs_soundness_lemma; split; trivial.
                    rewrite Hvars'; auto.
            }
            {
                case_eq (String.eqb elt i).
                + rewrite String.eqb_eq; move=> HEq2; destruct HEq2; assumption.
                + move=> HnotEq; apply HRel; unfold Complement, In; move=> HIn'.
                    rewrite <- not_true_iff_false in Hexists; apply Hexists.
                    rewrite iset.exists_spec; unfold iset.Exists.
                    exists elt.
                    destruct HIn' as [elt' []|].
                    by rewrite String.eqb_refl in HnotEq.
                    rewrite collect_bounddeqs_soundness_lemma; split; trivial.
                    rewrite Hvars'; auto.
            }
            all: rewrite <- not_true_iff_false in HnegMem; rewrite Hvars' in HnegMem.
            all: apply HRel; unfold Complement, In; move=> HIn'; destruct HIn' as [elt' []|elt' HIn'].
            1,3: apply HnegMem; auto.
            all: rewrite <- not_true_iff_false in Hexists; apply Hexists.
            all: rewrite iset.exists_spec; unfold iset.Exists.
            all: exists elt'.
            all: rewrite Hvars'; split; auto.
            all: rewrite collect_bounddeqs_soundness_lemma; trivial.
        }
    }
Qed.

Theorem clean_node_soudness arch prog:
    forall node param input,
        eval_node node arch prog param input <> None ->
        eval_node node arch prog param input =
        eval_node (clean_node node) arch prog param input.
Proof.
    unfold clean_node.
    move=> [id p_in p_out node_opt [temp_vars eqns| | |]]; simpl; trivial.
    unfold eval_node; simpl.
    move=> [] input; trivial.
    case (build_ctxt p_in (flatten_valueL (list_Value_of_list input) nil)); trivial.
    move=> ctxt HnoErr.
    assert (eval_deq_list arch prog ctxt eqns <> None) as HnoErr1.
    {
        move=> HEq; rewrite HEq in HnoErr; apply HnoErr; trivial.
    }
    pose (p := clean_in_deqs_soundness arch prog (deqL_of_list_deq eqns) (collect_vdecl p_out) ctxt ctxt); move: p.
    rewrite deqL_is_list_deq; move=> p.
    pose (p' := p HnoErr1 (context_srel_refl _ _) (context_srel_refl _ _)); move: p'; clear p.
    destruct (eval_deq_list arch prog ctxt eqns); simpl.
    2: by move=> ->; trivial.
    destruct (eval_deq_list arch prog ctxt (snd (clean_in_deqs (collect_vdecl p_out) eqns))); simpl.
    {
        induction p_out as [|a tl HRec]; simpl; trivial.
        move=> HRel; rewrite HRec.
        + rewrite HRel; trivial.
            unfold Ensembles.In; rewrite iset.mem_spec; rewrite iset.add_spec; auto.
        + simpl in HnoErr; move=> HEq; rewrite HEq in HnoErr; apply HnoErr; case (find_val c (VD_ID a)); trivial.
        + move=> x HIn; apply HRel; unfold Ensembles.In in *.
            rewrite iset.mem_spec; rewrite iset.mem_spec in HIn; rewrite iset.add_spec; auto.
    }
    {
        move=> [].
    }
Qed.
