Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST usuba_ASTProp arch
    list_relations termination_funs semantic_base semantic_base_proofs.

(* definition of specialization *)

Inductive is_specialization : nat -> indexing -> Prop :=
    | SpecInd : forall ae i,
        eval_arith_expr nil ae = Some i ->
        is_specialization i (IInd ae)
        (* is_specialization (ind1 ++ [:: i]) (ind2 ++ [:: IInd ae]) *)
    | SpecSlice : forall ae aeL i,
        List.In ae aeL ->
        eval_arith_expr nil ae = Some i ->
        is_specialization i (ISlice aeL)
    | SpecRange : forall ae1 ae2 i1 i2 i,
        eval_arith_expr nil ae1 = Some i1 ->
        eval_arith_expr nil ae2 = Some i2 ->
        ((i1 <= i /\ i <= i2) \/ (i2 <= i /\ i <= i1)) ->
        is_specialization i (IRange ae1 ae2)
.

Inductive is_specialization' : list nat -> list indexing -> Prop :=
    | AddPath : forall path_nat path_ind path_tl,
        list_rel is_specialization path_nat path_ind ->
        is_specialization' (path_nat ++ path_tl) path_ind
.

Inductive is_spec : ident -> list nat -> var -> Prop :=
    | ProjL : forall v ind1 ind2 ind3,
        list_rel is_specialization ind1 ind2 ->
        is_spec v (ind1 ++ ind3) (Index (Var v) ind2)
    | ProjR : forall v ind1 ind2 ind3,
        list_rel is_specialization ind1 ind2 ->
        is_spec v ind1 (Index (Var v) (ind2 ++ ind3)).

(* Properties about definitions *)

Fixpoint dtrees_length {A} (t : list_def_tree A) :=
    match t with
    | LDTnil => 0
    | LDTcons _ t => 1 + dtrees_length t
    end.

Inductive sub_dtree {A} : def_tree A -> def_tree A -> Prop :=
    | SDTBase : forall b t, sub_dtree (DTBase _ b) t
    | SDTRec : forall t1 t2, sub_dtrees t1 t2 -> sub_dtree (DTRec _ t1) (DTRec _ t2)
with sub_dtrees {A} : list_def_tree A -> list_def_tree A -> Prop :=
    | SLDTnil : sub_dtrees (LDTnil _) (LDTnil _)
    | SLDTcons : forall h1 h2 t1 t2,
        sub_dtree h1 h2 -> sub_dtrees t1 t2 ->
        sub_dtrees (LDTcons _ h1 t1) (LDTcons _ h2 t2).

Scheme sub_dtree_find := Induction for sub_dtree Sort Prop
with sub_dtrees_find := Induction for sub_dtrees Sort Prop.

Inductive same_dtree {A B} : def_tree A -> def_tree B -> Prop :=
    | SameDTBase : forall a b, same_dtree (DTBase _ a) (DTBase _ b)
    | SameDTRec : forall atrees btrees,
        same_dtrees atrees btrees ->
        same_dtree (DTRec _ atrees) (DTRec _ btrees)
with same_dtrees {A B} : list_def_tree A -> list_def_tree B -> Prop :=
    | SameDTnil : same_dtrees (LDTnil _) (LDTnil _)
    | SameDTcons : forall ahd bhd atl btl,
        same_dtree ahd bhd ->
        same_dtrees atl btl ->
        same_dtrees (LDTcons _ ahd atl) (LDTcons _ bhd btl).

Definition defined_in (v : ident) (l : list nat) (p : nat) (eL : list (seq var * expr)) : Prop :=
    exists vL e ind,
        nth_error eL p = Some (vL, e) /\
        list_rel is_specialization l ind /\
        (List.In (Index (Var v) ind) vL \/ (List.In (Var v) vL /\ ind = nil)).

Definition partial_defined_in (nskip : nat) (v : ident) (l : list nat) (p : nat) (eL : list (seq var * expr)) : Prop :=
    exists vL e ind,
        nth_error eL p = Some (vL, e) /\
        list_rel is_specialization l ind /\
        (exists i, nskip <= i /\
            (nth_error vL i = Some (Index (Var v) ind)
                \/ (nth_error vL i = Some (Var v) /\ ind = nil))).

Scheme def_tree_find := Induction for def_tree Sort Prop
with list_def_tree_find := Induction for list_def_tree Sort Prop.

Fixpoint valid_def_tree (v : ident) (t : def_tree nat) (l : list nat) (eL : list (seq var * expr)) : Prop :=
    match t with
    | DTBase eq_num => forall l' pos, list_rel_top eq l l' -> pos = eq_num /\ l = l' <-> defined_in v l' pos eL
    | DTRec trees => (forall pos, defined_in v l pos eL -> False) /\ valid_list_def_tree v trees 0 l eL
    end
with valid_list_def_tree v trees count l eL :=
    match trees with
    | LDTnil => True
    | LDTcons hd tl =>
        valid_def_tree v hd (l ++ [:: count]) eL /\
        valid_list_def_tree v tl (count.+1) l eL
    end.

Fixpoint partial_valid_def_tree (nb : nat) (v : ident) (t : def_tree int_or_awaits) (l : list nat) (eL : list (seq var * expr)) : Prop :=
    match t with
    | DTBase (IoAA _) =>
        (forall pos l', list_rel_top eq l l' -> nb <= pos -> defined_in v l'  pos eL -> False)
    | DTBase (IoAI eq_num) =>
        nb <= eq_num /\ forall pos l', nb <= pos -> list_rel_top eq l l' -> (pos = eq_num /\ l = l' <-> defined_in v l' pos eL)
    | DTRec trees =>
        (forall pos, nb <= pos -> defined_in v l pos eL -> False) /\
        partial_valid_list_def_tree nb v trees 0 l eL
    end
with partial_valid_list_def_tree nb v trees count l eL :=
    match trees with
    | LDTnil => True
    | LDTcons hd tl =>
        partial_valid_def_tree nb v hd (l ++ [:: count]) eL /\
        partial_valid_list_def_tree nb v tl (count.+1) l eL
    end.

Fixpoint partial_valid_def_tree' (nb nskip : nat) (v : ident) (t : def_tree int_or_awaits) (l : list nat) (eL : list (seq var * expr)) : Prop :=
    match t with
    | DTBase (IoAA _) =>
        (forall l', list_rel_top eq l l' -> partial_defined_in nskip v l' nb eL -> False) /\
        (forall pos l', list_rel_top eq l l' -> nb < pos -> defined_in v l' pos eL -> False)
    | DTBase (IoAI eq_num) =>
        nb <= eq_num /\
        forall pos l', nb <= pos -> list_rel_top eq l l' -> (pos = eq_num /\ l = l' <->
            if Nat.eqb pos nb
            then partial_defined_in nskip v l' pos eL
            else defined_in v l' pos eL)
    | DTRec trees =>
        (partial_defined_in nskip v l nb eL -> False) /\
        (forall pos, nb < pos -> defined_in v l pos eL -> False) /\
        partial_valid_list_def_tree' nb nskip v trees 0 l eL
    end
with partial_valid_list_def_tree' nb nskip v trees count l eL :=
    match trees with
    | LDTnil => True
    | LDTcons hd tl =>
        partial_valid_def_tree' nb nskip v hd (l ++ [:: count]) eL /\
        partial_valid_list_def_tree' nb nskip v tl (count.+1) l eL
    end.

(* Properties about uses *)

Fixpoint utrees_length trees :=
    match trees with
    | LUTnil => 0
    | LUTcons _ trees => (utrees_length trees).+1
    end.

Inductive sub_utree : use_tree -> use_tree -> Prop :=
    | SUTBase : forall u b t, sub_utree (UTBase u b) t
    | SUTRec : forall t1 t2 u1 u2, sub_utrees t1 t2 -> sub_utree (UTRec u1 t1) (UTRec u2 t2)
with sub_utrees : list_use_tree -> list_use_tree -> Prop :=
    | SLUTnil : sub_utrees LUTnil LUTnil
    | SLUTcons : forall h1 h2 t1 t2,
        sub_utree h1 h2 -> sub_utrees t1 t2 ->
        sub_utrees (LUTcons h1 t1) (LUTcons h2 t2).

Scheme sub_utree_find := Induction for sub_utree Sort Prop
with sub_utrees_find := Induction for sub_utrees Sort Prop.

Definition used_in (v : ident) (l : list nat) (p : nat) (eL : list (seq var * expr)) : Prop :=
    exists vL e ind,
        nth_error eL p = Some (vL, e) /\
        list_rel is_specialization l ind /\
        (Ensembles.In _ (expr_freefullvars e) (Index (Var v) ind) \/
        (Ensembles.In _ (expr_freefullvars e) (Var v) /\ ind = nil)).

Definition partial_used_in (v : ident) (l : list nat) (eL : list expr) : Prop :=
    exists ind,
        list_rel is_specialization l ind /\
        exists e',
            List.In e' eL /\
            (Ensembles.In _ (expr_freefullvars e') (Index (Var v) ind) \/
            (Ensembles.In _ (expr_freefullvars e') (Var v) /\ ind = nil)).    

Fixpoint valid_use_tree (v : ident) (t : use_tree) (l : list nat) (eL : list (seq var * expr)) : Prop :=
    match t with
    | UTBase posL typ => forall pos, List.In pos posL <-> used_in v l pos eL
    | UTRec posL trees =>
        (forall pos, List.In pos posL <-> used_in v l pos eL) /\
        valid_list_use_tree v trees 0 l eL
    end
with valid_list_use_tree v trees count l eL :=
    match trees with
    | LUTnil => True
    | LUTcons hd tl =>
        valid_use_tree v hd (l ++ [:: count]) eL /\
        valid_list_use_tree v tl (count.+1) l eL
    end.

Fixpoint partial_valid_use_tree (nb : nat) (v : ident) (t : use_tree) (l : list nat) (eL : list (seq var * expr)) : Prop :=
    match t with
    | UTBase posL typ => forall pos l', List.In pos posL /\ l' = nil <-> (nb <= pos /\ used_in v (l ++ l') pos eL)
    | UTRec posL trees =>
        (forall pos, List.In pos posL <-> (nb <= pos /\ used_in v l pos eL)) /\
        partial_valid_list_use_tree nb v trees 0 l eL
    end
with partial_valid_list_use_tree nb v trees count l eL :=
    match trees with
    | LUTnil => True
    | LUTcons hd tl =>
        partial_valid_use_tree nb v hd (l ++ [:: count]) eL /\
        partial_valid_list_use_tree nb v tl (count.+1) l eL
    end.

Fixpoint partial_valid_use_tree' (nb : nat) (eL : list expr) (v : ident) (t : use_tree) (l : list nat) (eqns : list (seq var * expr)) : Prop :=
    match t with
    | UTBase posL typ =>
        forall pos l', List.In pos posL /\ l' = nil <->
            (nb <= pos /\
                if nb =? pos
                then partial_used_in v (l ++ l') eL
                else used_in v (l ++ l') pos eqns)
    | UTRec posL trees =>
        (forall pos, List.In pos posL <-> (nb <= pos /\
            if nb =? pos
            then partial_used_in v l eL
            else used_in v l pos eqns)) /\
        partial_valid_list_use_tree' nb eL v trees 0 l eqns
    end
with partial_valid_list_use_tree' nb eL v trees count l eqns :=
    match trees with
    | LUTnil => True
    | LUTcons hd tl =>
        partial_valid_use_tree' nb eL v hd (l ++ [:: count]) eqns /\
        partial_valid_list_use_tree' nb eL v tl (count.+1) l eqns
    end.
    
(* valid access properties *)

Definition eval_lt (len : nat) (ae : arith_expr) : Prop :=
    match eval_arith_expr nil ae with
    | None => False
    | Some i => i < len
    end. 

Fixpoint valid_access (t : typ) (indexing : list indexing) : Prop :=
    match t with
    | Array t len =>
        match indexing with
        | nil => True
        | ind :: tl =>
            valid_access t tl /\
            match ind with
            | IInd ae => eval_lt len ae
            | IRange ae1 ae2 => eval_lt len ae1 /\ eval_lt len ae2
            | ISlice aeL => Forall (eval_lt len) aeL /\ aeL <> nil
            end 
        end
    | _ => indexing = nil
    end.

Fixpoint valid_dtree_access {A} (t : def_tree A) (indexing : list indexing) : Prop :=
    match indexing with
    | nil => True
    | ind :: tl =>
        match t with
        | DTRec trees =>
            match match ind with
                | IInd ae =>
                    i <- eval_arith_expr nil ae; Some [:: i]
                | IRange ae1 ae2 =>
                    i1 <- eval_arith_expr nil ae1;
                    i2 <- eval_arith_expr nil ae2;
                    Some (gen_range i1 i2)
                | ISlice aeL =>
                    fold_right (fun ae l => l' <- l; i <- eval_arith_expr nil ae; Some (i::l')) (Some nil) aeL
                end
            with
            | None => False
            | Some iL =>
                iL <> nil /\
                Forall (fun i => i < dtrees_length trees) iL /\
                valid_dtrees_access trees 0 iL tl
            end
        | DTBase _ => false
        end
    end
with valid_dtrees_access {A} (t : list_def_tree A) (pos : nat) (indices : list nat) (indexing : list indexing) : Prop :=
    match t with
    | LDTnil => True
    | LDTcons hd tl =>
        valid_dtrees_access tl pos.+1 indices indexing /\
        if List.existsb (Nat.eqb pos) indices
        then valid_dtree_access hd indexing
        else True
    end.

Fixpoint valid_dtree_access' {A} (t : def_tree A) (indexing : list nat) : Prop :=
    match indexing with
    | nil => True
    | ind :: tl =>
        match t with
        | DTRec trees =>
            ind < dtrees_length trees /\
            valid_dtrees_access' trees ind tl
        | DTBase _ => false
        end
    end
with valid_dtrees_access' {A} (t : list_def_tree A) (ind : nat) (indexing : list nat) : Prop :=
    match t with
    | LDTnil => False
    | LDTcons hd tl =>
        match ind with
        | 0 => valid_dtree_access' hd indexing
        | S ind => valid_dtrees_access' tl ind indexing
        end
    end.

Fixpoint valid_utree_access (t : use_tree) (indexing : list indexing) : Prop :=
    match indexing with
    | nil => True
    | ind :: tl =>
        match t with
        | UTRec _ trees =>
            match match ind with
                | IInd ae =>
                    i <- eval_arith_expr nil ae; Some [:: i]
                | IRange ae1 ae2 =>
                    i1 <- eval_arith_expr nil ae1;
                    i2 <- eval_arith_expr nil ae2;
                    Some (gen_range i1 i2)
                | ISlice aeL =>
                    fold_right (fun ae l => l' <- l; i <- eval_arith_expr nil ae; Some (i::l')) (Some nil) aeL
                end
            with
            | None => False
            | Some iL =>
                iL <> nil /\
                Forall (fun i => i < utrees_length trees) iL /\
                valid_utrees_access trees 0 iL tl
            end
        | UTBase _ _ => false
        end
    end
with valid_utrees_access (t : list_use_tree) (pos : nat) (indices : list nat) (indexing : list indexing) : Prop :=
    match t with
    | LUTnil => True
    | LUTcons hd tl =>
        valid_utrees_access tl pos.+1 indices indexing /\
        if List.existsb (Nat.eqb pos) indices
        then valid_utree_access hd indexing
        else True
    end.

Fixpoint valid_utree_access' (t : use_tree) (indexing : list nat) : Prop :=
    match indexing with
    | nil => True
    | ind :: tl =>
        match t with
        | UTRec _ trees =>
            ind < utrees_length trees /\
            valid_utrees_access' trees ind tl
        | UTBase _ _ => false
        end
    end
with valid_utrees_access' (t : list_use_tree) (ind : nat) (indexing : list nat) : Prop :=
    match t with
    | LUTnil => False
    | LUTcons hd tl =>
        match ind with
        | 0 => valid_utree_access' hd indexing
        | S ind => valid_utrees_access' tl ind indexing
        end
    end.

Definition valid_var tctxt v :=
    match v with
    | Index (Index _ _) _ => False
    | Index (Var v) ind =>
        match find_val tctxt v with
        | Some t => valid_access t ind
        | None => False
        end
    | Var v => find_val tctxt v <> None
    end.

Definition valid_var_dtree {A} deps v :=
    match v with
    | Index (Index _ _) _ => False
    | Index (Var v) ind =>
        match find_val deps v with
        | Some t => @valid_dtree_access A t ind
        | None => False
        end
    | Var v => find_val deps v <> None
    end.

Definition dtree_valid_access_if_var {A} v var (defs : def_tree A) :=
    match var with
    | Var v' => True
    | Index (Var v') ind =>
        if ident_beq v v'
        then valid_dtree_access defs ind
        else True
    | _ => False
    end.
    
Definition valid_var_dtree' {A} deps v :=
    match v with
    | Index (Index _ _) _ => False
    | Index (Var v) ind =>
        match find_val deps v with
        | Some (Some t) => @valid_dtree_access A t ind
        | Some None => True
        | None => False
        end
    | Var v => find_val deps v <> None
    end.

Definition valid_var_utree deps v :=
    match v with
    | Index (Index _ _) _ => False
    | Index (Var v) ind =>
        match find_val deps v with
        | Some t => valid_utree_access t ind
        | None => False
        end
    | Var v => find_val deps v <> None
    end.

Definition utree_valid_access_if_var v var uses :=
    match var with
    | Var v' => True
    | Index (Var v') ind =>
        if ident_beq v v'
        then valid_utree_access uses ind
        else True
    | _ => False
    end.
    
(* type soundness of trees *)

Fixpoint def_tree_of_type (tree : def_tree int_or_awaits) (t : typ) : Prop :=
    match tree with
    | DTBase (IoAA t') => t = t'
    | DTBase (IoAI _) => True
    | DTRec trees =>
        match t with
        | Array t len => list_def_tree_of_type trees t len
        | _ => False
        end
    end
with list_def_tree_of_type (trees : list_def_tree int_or_awaits) (t : typ) (l : nat) : Prop :=
    match trees with
    | LDTnil => l = 0
    | LDTcons hd tl =>
        def_tree_of_type hd t /\
        match l with
        | 0 => False
        | S l => list_def_tree_of_type tl t l
        end
    end.

Fixpoint def_tree_of_type' (tree : def_tree nat) (t : typ) : Prop :=
    match tree with
    | DTBase _ => True
    | DTRec trees =>
        match t with
        | Array t len => list_def_tree_of_type' trees t len
        | _ => False
        end
    end
with list_def_tree_of_type' (trees : list_def_tree nat) (t : typ) (l : nat) : Prop :=
    match trees with
    | LDTnil => l = 0
    | LDTcons hd tl =>
        def_tree_of_type' hd t /\
        match l with
        | 0 => False
        | S l => list_def_tree_of_type' tl t l
        end
    end.
    
Fixpoint use_tree_of_type (tree : use_tree) (t : typ) : Prop :=
    match tree with
    | UTBase _ t' => t = t'
    | UTRec _ trees =>
        match t with
        | Array t len => list_use_tree_of_type trees t len
        | _ => False
        end
    end
with list_use_tree_of_type (trees : list_use_tree) (t : typ) (l : nat) : Prop :=
    match trees with
    | LUTnil => l = 0
    | LUTcons hd tl =>
        use_tree_of_type hd t /\
        match l with
        | 0 => False
        | S l => list_use_tree_of_type tl t l
        end
    end.

(* Relation between trees *)

Definition r_dutree eqns v (p : option (def_tree nat) * use_tree) :=
    let (defs, uses) := p in
        match defs with
        | None =>
            valid_use_tree v uses nil eqns /\
            (forall i path, defined_in v path i eqns -> False) /\
            Forall (fun p : list var * expr =>
                forall var, Ensembles.In _ (expr_freefullvars p.2) var -> utree_valid_access_if_var v var uses) eqns
        | Some defs =>
            valid_def_tree v defs nil eqns /\ valid_use_tree v uses nil eqns /\
            (exists typ,
                def_tree_of_type' defs typ /\ use_tree_of_type uses typ) /\
            Forall (fun p : list var * expr => let (vars, expr) := p in
                Forall (fun var => dtree_valid_access_if_var v var defs) vars /\
                forall var, Ensembles.In _ (expr_freefullvars expr) var -> utree_valid_access_if_var v var uses) eqns
        end.

(* TODO find section name *)

Fixpoint dtree_defined (tree : def_tree nat) (path : list nat) (eq_num : nat) : Prop :=
    match tree with
    | DTBase eq_num' => path = nil /\ eq_num' = eq_num
    | DTRec trees =>
        match path with
        | nil => False
        | pos :: path =>
            dtrees_defined trees path pos eq_num
        end
    end
with dtrees_defined trees path pos eq_num :=
    match trees with 
    | LDTnil => False
    | LDTcons hd tl =>
        match pos with
        | 0 =>
            dtree_defined hd path eq_num
        | S pos =>
            dtrees_defined tl path pos eq_num
        end
    end.

Fixpoint utree_used (tree : use_tree) (path : list nat) (eq_num : nat) : Prop :=
    match tree with
    | UTBase uses _ => path = nil /\ List.In eq_num uses
    | UTRec uses trees =>
        match path with
        | nil => List.In eq_num uses
        | pos :: path =>
            utrees_used trees path pos eq_num
        end
    end
with utrees_used trees path pos eq_num :=
    match trees with 
    | LUTnil => False
    | LUTcons hd tl =>
        match pos with
        | 0 =>
            utree_used hd path eq_num
        | S pos =>
            utrees_used tl path pos eq_num
        end
    end.

(* Definition of topological sort *)


Definition is_topological_sort (eqns : list (list var * expr)) (ord : list nat) : Prop :=
        length eqns = length ord /\
        forall v path_d path_u p_used p_def,
            list_rel_top eq path_u path_d ->
            used_in v path_u p_used eqns ->
            defined_in v path_d p_def eqns ->
            exists p_used' p_def',
                nth_error ord p_used = Some p_used' /\
                nth_error ord p_def = Some p_def' /\
                p_def' < p_used'.

