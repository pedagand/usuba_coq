Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST usuba_ASTProp arch semantic_base topological_sort.

(* def trees *)

Inductive def_tree (t : Type) :=
    | DTBase of t
    | DTRec of list_def_tree t
with list_def_tree (t : Type):=
    | LDTnil
    | LDTcons : def_tree t -> list_def_tree t -> list_def_tree t.

Inductive int_or_awaits :=
    | IoAI of nat
    | IoAA of typ.


Fixpoint build_def_trees {A : Type} (pos : nat) (left : nat) (indices : list nat) (good_tree bad_tree : def_tree A) : list_def_tree A :=
    match left with
    | 0 => LDTnil _
    | S left' =>
        if List.existsb (Nat.eqb pos) indices
        then LDTcons _ good_tree (build_def_trees (S pos) left' indices good_tree bad_tree)
        else LDTcons _  bad_tree (build_def_trees (S pos) left' indices good_tree bad_tree)
    end.

Fixpoint build_def_tree_from_type (path : list indexing) (t : typ) (eq_num : nat) : option (def_tree int_or_awaits) :=
    match path with
    | nil => Some (DTBase _ (IoAI eq_num))
    | hd::tl =>
        match t with
        | Array t' len =>
            next_tree <- build_def_tree_from_type tl t' eq_num;
            indices <- match hd with
                | IInd ae => i <- eval_arith_expr nil ae; Some [:: i]
                | ISlice aeL =>
                    fold_right (fun ae l => l' <- l; i <- eval_arith_expr nil ae; Some (i::l')) (Some nil) aeL
                | IRange ae1 ae2 =>
                    i1 <- eval_arith_expr nil ae1;
                    i2 <- eval_arith_expr nil ae2;
                    Some (gen_range i1 i2)
                end;
            if List.forallb (fun i => i <? len) indices && List.existsb (fun _ => true) indices
            then
                Some (DTRec _ (build_def_trees 0 len indices next_tree (DTBase _ (IoAA t'))))
            else
                None
        | _ => None
        end
    end.

Fixpoint update_def_tree (path : list indexing) (eq_num : nat) (t : def_tree int_or_awaits) : option (def_tree int_or_awaits) :=
    match t with
    | DTBase (IoAI _) => None
    | DTBase (IoAA typ) => build_def_tree_from_type path typ eq_num
    | DTRec trees =>
        match path with
        | nil => None
        | hd::path_tl =>
            indices <- match hd with
                | IInd ae => i <- eval_arith_expr nil ae; Some [:: i]
                | ISlice aeL =>
                    fold_right (fun ae l => l' <- l; i <- eval_arith_expr nil ae; Some (i::l')) (Some nil) aeL
                | IRange ae1 ae2 =>
                    i1 <- eval_arith_expr nil ae1;
                    i2 <- eval_arith_expr nil ae2;
                    Some (gen_range i1 i2)
                end;
            trees' <- update_def_trees 0 path_tl eq_num trees indices;
            Some (DTRec _ trees')
        end
    end
with update_def_trees (pos : nat) (path_tl : list indexing) (eq_num : nat) (t : list_def_tree int_or_awaits) (indices : list nat) :=
    match t with
    | LDTnil =>
        if List.forallb (fun i => i <? pos) indices && List.existsb (fun _ => true) indices
        then Some (LDTnil _)
        else None
    | LDTcons hd tl =>
        tl' <- update_def_trees (pos + 1) path_tl eq_num tl indices;
        if List.existsb (Nat.eqb pos) indices
        then
            hd' <- update_def_tree path_tl eq_num hd;
            Some (LDTcons _ hd' tl')
        else
            Some (LDTcons _ hd tl')
    end.

Fixpoint update_vars (vars : seq bvar) (pos : nat) (dependancies : list (ident * def_tree int_or_awaits)) :=
    match vars with
    | nil => Some dependancies
    | (v, ind)::tl =>
        dependancies' <- update_vars tl pos dependancies;
        update_ctxt dependancies' v (update_def_tree ind pos)
    end.
    
(* use trees *)

Inductive use_tree :=
    | UTBase : list nat -> typ -> use_tree
    | UTRec : list nat -> list_use_tree -> use_tree
with list_use_tree :=
    | LUTnil
    | LUTcons : use_tree -> list_use_tree -> list_use_tree.

Scheme use_tree_find := Induction for use_tree Sort Prop
with list_use_tree_find := Induction for list_use_tree Sort Prop.

Fixpoint build_use_trees (pos : nat) (left : nat) (indices : list nat) (good_tree bad_tree : use_tree) : list_use_tree :=
    match left with
    | 0 => LUTnil
    | S left' =>
        if List.existsb (Nat.eqb pos) indices
        then LUTcons good_tree (build_use_trees (S pos) left' indices good_tree bad_tree)
        else LUTcons  bad_tree (build_use_trees (S pos) left' indices good_tree bad_tree)
    end.

Fixpoint build_use_tree_from_type (path : list indexing) (l : list nat) (t : typ) (eq_num : nat) : option use_tree :=
    match path with
    | nil => Some (UTBase (eq_num::l) t)
    | hd::tl =>
        match t with
        | Array t' len =>
            next_tree <- build_use_tree_from_type tl nil t' eq_num;
            indices <- match hd with
                | IInd ae => i <- eval_arith_expr nil ae; Some [:: i]
                | ISlice aeL =>
                    fold_right (fun ae l => l' <- l; i <- eval_arith_expr nil ae; Some (i::l')) (Some nil) aeL
                | IRange ae1 ae2 =>
                    i1 <- eval_arith_expr nil ae1;
                    i2 <- eval_arith_expr nil ae2;
                    Some (gen_range i1 i2)
                end;
            if List.forallb (fun i => i <? len) indices && List.existsb xpredT indices
            then
                Some (UTRec l (build_use_trees 0 len indices next_tree (UTBase nil t')))
            else
                None
        | _ => None
        end
    end.

Fixpoint update_use_tree (path : list indexing) (eq_num : nat) (t : use_tree) : option use_tree :=
    match t with
    | UTBase l typ => 
        build_use_tree_from_type path l typ eq_num
    | UTRec posL trees =>
        match path with
        | nil =>
            Some (UTRec (eq_num::posL) trees)
        | hd::path_tl =>
            indices <- match hd with
                | IInd ae => i <- eval_arith_expr nil ae; Some [:: i]
                | ISlice aeL =>
                    fold_right (fun ae l => l' <- l; i <- eval_arith_expr nil ae; Some (i::l')) (Some nil) aeL
                | IRange ae1 ae2 =>
                    i1 <- eval_arith_expr nil ae1;
                    i2 <- eval_arith_expr nil ae2;
                    Some (gen_range i1 i2)
                end;
            trees' <- update_use_trees 0 path_tl eq_num trees indices;
            Some (UTRec posL trees')
        end
    end
with update_use_trees (pos : nat) (path_tl : list indexing) (eq_num : nat) (t : list_use_tree) (indices : list nat) :=
    match t with
    | LUTnil =>
        if List.forallb (fun i => i <? pos) indices && List.existsb xpredT indices
        then Some LUTnil
        else None
    | LUTcons hd tl =>
        tl' <- update_use_trees (pos + 1) path_tl eq_num tl indices;
        if List.existsb (Nat.eqb pos) indices
        then
            hd' <- update_use_tree path_tl eq_num hd;
            Some (LUTcons hd' tl')
        else
            Some (LUTcons hd tl')
    end.

Fixpoint update_expr (e : expr) (pos : nat) (dependancies : list (ident * use_tree)) :=
    match e with
    | Const _ _ => Some dependancies
    | ExpVar (Var v) | Shuffle (Var v) _ =>
        update_ctxt dependancies v (update_use_tree nil pos)
    | ExpVar (Index (Var v) ind) | Shuffle (Index (Var v) ind) _ =>
        update_ctxt dependancies v (update_use_tree ind pos)
    | ExpVar (Index (Index _ _) _) | Shuffle (Index (Index _ _) _) _ => None
    | Tuple el | BuildArray el | Fun _ _ _ _ el =>
        update_list_expr el pos dependancies
    | Not e | Shift _ e _ | Bitmask e _ | Coercion e _ =>
        update_expr e pos dependancies
    | Log _ e1 e2 | Arith _ e1 e2 | Pack e1 e2 _ =>
        dependancies' <- update_expr e1 pos dependancies;
        update_expr e2 pos dependancies'
    end
with update_list_expr el pos dependancies :=
    match el with
    | Enil => Some dependancies
    | ECons hd tl =>
        dependancies' <- update_expr hd pos dependancies;
        update_list_expr tl pos dependancies'
    end.

(* unification of both types of trees *)

Fixpoint build_definitions_inner (pos : nat) (tctxt : list (ident * typ)) (eqns : list (seq bvar * expr)) :=
    match eqns with
    | nil => Some (map_ctxt (fun t => DTBase _ (IoAA t)) tctxt, map_ctxt (fun t => UTBase nil t) tctxt)
    | (vars, e)::tl =>
        (defs, uses) <- build_definitions_inner (S pos) tctxt tl;
        defs' <- update_vars vars pos defs;
        uses' <- update_expr e pos uses;
        Some (defs', uses')
    end.

Fixpoint remove_await_tree (t : def_tree int_or_awaits) : option (def_tree nat) :=
    match t with
    | DTBase (IoAA _) => None
    | DTBase (IoAI i) => Some (DTBase _ i)
    | DTRec trees =>
        trees' <- remove_await_trees trees;
        Some (DTRec _ trees')
    end
with remove_await_trees trees : option (list_def_tree nat) :=
    match trees with
    | LDTnil => Some (LDTnil _)
    | LDTcons hd tl =>
        hd' <- remove_await_tree hd;
        tl' <- remove_await_trees tl;
        Some (LDTcons _ hd' tl')
    end.

Fixpoint clean_def_tree ctxt : option (list (ident * option (def_tree nat))):=
    match ctxt with
    | nil => Some nil
    | (v, DTBase (IoAA _))::tl =>
        tl' <- clean_def_tree tl;
        Some ((v, None) :: tl')
    | (v, t)::tl =>
        t' <- remove_await_tree t;
        tl' <- clean_def_tree tl;
        Some ((v, Some t')::tl')
    end.

Definition build_definitions tctxt eqns :=
    (defs, uses) <- build_definitions_inner 0 tctxt eqns;
    defs' <- clean_def_tree defs;
    Some (defs', uses).
    
(*
    Construction of the relation function for our graph :

    We define deps as nth i deps =
        {all equations that depends on a definition in i }
*)


Fixpoint extract_uses (uses : use_tree) : list nat :=
    match uses with
    | UTBase l _ => l
    | UTRec l trees => l ++ extract_uses_l trees
    end
with extract_uses_l trees :=
    match trees with
    | LUTnil => nil
    | LUTcons hd tl => extract_uses hd ++ extract_uses_l tl
    end.

Fixpoint extract_defs (defs : def_tree nat) : list nat :=
    match defs with
    | DTBase i => [:: i]
    | DTRec trees => extract_defs_l trees
    end
with extract_defs_l trees :=
    match trees with
    | LDTnil => nil
    | LDTcons hd tl => extract_defs hd ++ extract_defs_l tl
    end.

Fixpoint update_list {A} (l : list A) (pos : nat) (f : A -> A) :=
    match l with
    | nil => nil
    | hd :: tl =>
        match pos with
        | 0 => f hd :: tl
        | S pos => hd :: update_list tl pos f
        end
    end.

Fixpoint add_deps (deps : list (list nat)) (defs : def_tree nat) (uses : use_tree) (above_uses : list nat) : list (list nat) :=
    match defs with
    | DTBase i =>
        update_list deps i (fun l => extract_uses uses ++ above_uses ++ l)
    | DTRec dtrees =>
        match uses with
        | UTBase useL _ =>
            fold_left (fun deps p => update_list deps p (fun l => useL ++ above_uses ++ l)) (extract_defs_l dtrees) deps
        | UTRec l utrees =>
            add_deps_trees deps dtrees utrees (l ++ above_uses)
        end
    end
with add_deps_trees deps dtrees utrees above_uses :=
    match dtrees with
    | LDTnil => deps
    | LDTcons dhd dtl =>
        match utrees with
        | LUTnil => deps
        | LUTcons uhd utl =>
            add_deps_trees (add_deps deps dhd uhd above_uses) dtl utl above_uses
        end
    end.

Fixpoint gen_list {A} (el : A) n :=
    match n with
    | 0 => nil
    | S n => el :: gen_list el n
    end.

Definition update_all (trees : list (option (def_tree nat) * use_tree)) len :=
    fold_right (fun (p : option (def_tree nat) * use_tree) deps =>
        match p.1 with
        | None => deps
        | Some defs => add_deps deps defs p.2 nil
        end)
        (gen_list nil len) trees.

Definition test_if_inf (deps : list (list nat)) (i1 i2 : nat) : bool :=
    match nth_error deps i1 with
    | Some l => List.existsb (Nat.eqb i2) l
    | None => false
    end.

Fixpoint test_distinct {A} (l : list (ident * A)) (up : list ident) : bool :=
    match l with
    | nil => true
    | (i, _) :: tl =>
        (negb (List.existsb (ident_beq i) up)) && test_distinct tl (i :: up)
    end.

Definition build_topological_sort tctxt eqns :=
    if test_distinct tctxt nil
    then
        (defs, uses) <- build_definitions tctxt eqns;
        build_order (test_if_inf (update_all (zip (map snd defs) (map snd uses)) (length eqns))) (length eqns)
    else None.

Definition eval_to_nat i ae :=
    match eval_arith_expr nil ae with
    | Some i' => Nat.eqb i i'
    | None => false
    end.

Fixpoint is_spec_b path ind :=
    match path with
    | nil =>
        match ind with
        | nil => true
        | _ => false
        end
    | i :: path_tl =>
        match ind with
        | nil => true
        | IInd ae :: ind_tl =>
            eval_to_nat i ae && is_spec_b path_tl ind_tl
        | ISlice aeL :: ind_tl =>
            List.existsb (eval_to_nat i) aeL && is_spec_b path_tl ind_tl
        | IRange ae1 ae2 :: ind_tl =>
            match eval_arith_expr nil ae1 with
            | Some i1 =>
                match eval_arith_expr nil ae2 with
                | Some i2 =>
                    (((i1 <= i) && (i <= i2)) || ((i2 <= i) && (i <= i1)))
                        && is_spec_b path_tl ind_tl
                | None => false
                end
            | None => false
            end
        end
    end.


Definition is_generalization (v : ident) (path : list nat) (var : bvar) : bool :=
    let (v', ind) := var in
        ident_beq v v' && is_spec_b path ind
.

Fixpoint generalization_in (v : ident) (path : list nat) (vars : list bvar) : bool :=
    match vars with
    | nil => false
    | v' :: tl =>
        if is_generalization v path v'
        then true
        else generalization_in v path tl
    end.
    