Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import seq ssrnat.

From Usuba Require Import ident usuba_AST arch semantic_base.

Inductive value_tree : Type :=
    | VTBase : Sum Z typ -> value_tree
    | VTRec : list_value_tree -> value_tree
with list_value_tree : Type :=
    | LVTnil : list_value_tree
    | LVTcons : value_tree -> list_value_tree -> list_value_tree
.

Definition context : Type := list (ident * (dir * value_tree)).

Fixpoint expr_list_of_list (el : seq expr) : expr_list :=
    match el with 
    | nil => Enil
    | hd :: tl => ECons hd (expr_list_of_list tl)
    end.

Fixpoint expr_of_val (form : list nat) (t : typ) (input : list Z) : option expr :=
    match form with
    | nil =>
        match input with
        | [:: i] => Some (Const i (Some t))
        | _ => None
        end
    | form_hd :: form_tl =>
        input' <- split_into_segments form_hd (prod_list form_tl) input;
        l' <- remove_option_from_list (map (expr_of_val form_tl t) input');
        Some (BuildArray (expr_list_of_list l'))
    end.

Definition typ_of_dir (d : dir) : option typ :=
    match d with
    | DirH n => Some (Uint Hslice (Mint n))
    | DirV n => Some (Uint Vslice (Mint n))
    | DirB   => Some (Uint Bslice (Mint 1))
    | DirUnknow | DirH_ | DirV_ | Dir_S _ => None 
    end.

Definition val_to_expr (i : @cst_or_int Z) : option expr :=
    match i with
    | CoIL n => Some (Const n None)
    | CoIR d v form =>
        typ <- typ_of_dir d;
        expr_of_val form typ v
    end
.

Fixpoint list_val_to_expr_list (i : list (@cst_or_int Z)) : option expr_list :=
    match i with
    | nil => Some Enil
    | hd :: tl =>
        vhd <- val_to_expr hd;
        vtl <- list_val_to_expr_list tl;
        Some (ECons vhd vtl)
    end
.

Definition list_val_to_expr (i : list (@cst_or_int Z)) : option expr :=
    el <- list_val_to_expr_list i;
    Some (Tuple el)
.

Fixpoint collect_all_value_tree (tree : value_tree) : Sum (list Z * list nat) unit :=
    match tree with
    | VTBase (SumR _) => SumR tt
    | VTBase (SumL v) => SumL ([:: v], nil)
    | VTRec trees =>
        match collect_all_list_value_tree trees with
        | SumR tt | SumL None => SumR tt
        | SumL (Some (values, form, len)) => SumL (values, len :: form)
        end
    end
with collect_all_list_value_tree (trees : list_value_tree) : Sum (option (list Z * list nat * nat)) unit :=
    match trees with
    | LVTnil => SumL None
    | LVTcons hd tl =>
        match collect_all_value_tree hd with
        | SumR tt => SumR tt
        | SumL (hd', form_hd) =>
            match collect_all_list_value_tree tl with
            | SumR tt => SumR tt
            | SumL None => SumL (Some (hd', form_hd, 1))
            | SumL (Some (tl', form_tl, len)) =>
                if list_beq _ (Nat.eqb) form_hd form_tl
                then SumL (Some (hd' ++ tl', form_tl, len.+1))
                else SumR tt (* Should not happen *)
            end
        end
    end
.

Fixpoint get_pos (trees : list_value_tree) (pos : nat) : option value_tree :=
    match trees with
    | LVTnil => None
    | LVTcons hd tl =>
        match pos with
        | 0 => Some hd
        | S pos => get_pos tl pos
        end
    end
.

Fixpoint combine_values (args : seq (option (Sum value_tree unit))) :  option (Sum list_value_tree unit) :=
    match args with 
    | nil => Some (SumL LVTnil)
    | res :: tl =>
        match combine_values tl with
        | None => None
        | Some (SumR tt) => Some (SumR tt) 
        | Some (SumL trees) =>
            match res with
            | None => None
            | Some (SumR tt) => Some (SumR tt)
            | Some (SumL tree) =>
                Some (SumL (LVTcons tree trees))
            end
        end
    end
.

Fixpoint val_of_value_tree (path : seq indexing) (tree : value_tree) : option (Sum value_tree unit) :=
    match path with
    | nil => Some (SumL tree)
    | ind :: path_tl =>
        match tree with
        | VTBase (SumR _) => Some (SumR tt)
        | VTBase (SumL v) => None
        | VTRec trees =>
            match ind with
            | IInd ae =>
                i <- eval_arith_expr nil ae;
                tree <- get_pos trees i;
                val_of_value_tree path_tl tree
            | IRange ae1 ae2 =>
                i1 <- eval_arith_expr nil ae1;
                i2 <- eval_arith_expr nil ae2;
                let trees' := map (fun i =>
                    tree <- get_pos trees i;
                    val_of_value_tree path_tl tree) (gen_range i1 i2) in
                match combine_values trees' with
                | None => None
                | Some (SumR tt) => Some (SumR tt)
                | Some (SumL trees'') => Some (SumL (VTRec trees''))
                end
            | ISlice aeL =>
                iL <- remove_option_from_list (map (eval_arith_expr nil) aeL);
                let trees' := map (fun i =>
                    tree <- get_pos trees i;
                    val_of_value_tree path_tl tree) iL in
                match combine_values trees' with
                | None => None
                | Some (SumR tt) => Some (SumR tt)
                | Some (SumL trees'') => Some (SumL (VTRec trees''))
                end
            end
        end
    end
.

Fixpoint eval_var_inner (var : var) (c : context) : option (Sum (dir * value_tree) unit) :=
    match var with
    | Var ident =>
        (dir, tree) <- find_val c ident;
        Some (SumL (dir, tree))
    | Index svar ind =>
        match eval_var_inner svar c with
        | None => None
        | Some (SumR tt) => Some (SumR tt)
        | Some (SumL (dir, tree)) =>
            match val_of_value_tree ind tree with
            | None => None
            | Some (SumR tt) => Some (SumR tt)
            | Some (SumL tree') => Some (SumL (dir, tree'))
            end
        end
    end
.

Definition eval_var (var : var) (c : context) : option (Sum (@cst_or_int Z) expr) :=
    match eval_var_inner var c with
    | None => None
    | Some (SumR tt) => Some (SumR (ExpVar var))
    | Some (SumL (dir, tree)) =>
        match collect_all_value_tree tree with
        | SumR tt => Some (SumR (ExpVar var))
        | SumL (val, form) =>
            Some (SumL (CoIR dir val form))
        end
    end
.

Fixpoint eval_expr (arch : architecture) (prog : prog_ctxt) (ctxt : context) (e : expr) : option (Sum (list (@cst_or_int Z)) expr) :=
    match e with
        | Const n None => Some (SumL (CoIL n::nil))
        | Const n (Some typ) => 
            v <- build_integer typ n; Some (SumL v)
        | ExpVar var =>
            v <- eval_var var ctxt;
            match v with
            | SumL v => Some (SumL [:: v])
            | SumR e => Some (SumR e)
            end
        | BuildArray el => 
            o <- eval_expr_list' arch prog ctxt el;
            match o with
            | SumR el' => Some (SumR (BuildArray el'))
            | SumL (Some (len, values, form, d)) =>
                Some (SumL [:: CoIR d values (len::form)])
            | SumL None => None
            end
        | Tuple el =>
            s <- eval_expr_list arch prog ctxt el;
            Some (match s with
                | SumR el' => SumR (Tuple el')
                | SumL val => SumL val
            end)
        | Not e =>
            s <- eval_expr arch prog ctxt e;
            match s with
            | SumR e' => Some (SumR (Not e'))
            | SumL v => 
                option_map SumL (eval_monop (arith_wrapper (IMPL_LOG arch) lnot) v)
            end
        | Log op e1 e2 =>
            v1 <- eval_expr arch prog ctxt e1;
            v2 <- eval_expr arch prog ctxt e2;
            f <- match op with
                | And | Masked And =>   Some (arith_wrapper (IMPL_LOG arch) land)
                | Or | Masked Or =>     Some (arith_wrapper (IMPL_LOG arch) lor)
                | Xor | Masked Xor =>   Some (arith_wrapper (IMPL_LOG arch) lxor)
                | Andn | Masked Andn => Some (arith_wrapper (IMPL_LOG arch) landn)
                | Masked (Masked _) => None
            end;
            match v1 with
            | SumR e1' =>
                match v2 with
                | SumR e2' => Some (SumR (Log op e1' e2'))
                | SumL v2 =>
                    e2' <- list_val_to_expr v2;
                    Some (SumR (Log op e1' e2'))
                end
            | SumL v1 =>
                match v2 with
                | SumR e2' =>
                    e1' <- list_val_to_expr v1;
                    Some (SumR (Log op e1' e2'))
                | SumL v2 =>
                    val <- eval_binop f v1 v2;
                    Some (SumL val)
                end
            end
        | Arith op e1 e2 =>
            v1 <- eval_expr arch prog ctxt e1;
            v2 <- eval_expr arch prog ctxt e2;
            let f := match op with
                | Add => arith_wrapper (IMPL_ARITH arch) add_fun
                | Sub => arith_wrapper (IMPL_ARITH arch) sub_fun
                | Div => arith_wrapper (IMPL_ARITH arch) div_fun
                | Mod => arith_wrapper (IMPL_ARITH arch) mod_fun
                | Mul => arith_wrapper (IMPL_ARITH arch) mul_fun
            end in
            match v1 with
            | SumR e1' =>
                match v2 with
                | SumR e2' => Some (SumR (Arith op e1' e2'))
                | SumL v2 =>
                    e2' <- list_val_to_expr v2;
                    Some (SumR (Arith op e1' e2'))
                end
            | SumL v1 =>
                match v2 with
                | SumR e2' =>
                    e1' <- list_val_to_expr v1;
                    Some (SumR (Arith op e1' e2'))
                | SumL v2 =>
                    option_map SumL (eval_binop f v1 v2)
                end
            end
        | Shift op e1 e2 =>
            v1 <- eval_expr arch prog ctxt e1;
            v2 <- eval_arith_expr nil e2;
            match v1 with
            | SumR e1' => Some (SumR (Shift op e1' (Const_e (Z.of_nat v2))))
            | SumL v1 =>
                option_map SumL (eval_shift arch op v1 v2)
            end
        | Shuffle v l => None
        | Bitmask e ae => None
        | Pack e1 e2 None => None
        | Pack e1 e2 (Some t) => None
        | Fun id el =>
            args <- eval_expr_list arch prog ctxt el;
            f <- find_val prog id;
            match args with
            | SumR el' => Some (SumR (Fun id el'))
            | SumL args =>
                l_val <- f None args;
                Some (SumL (linearize_list_value l_val nil))
            end
        | Fun_v id ie el =>
            args <- eval_expr_list arch prog ctxt el;
            i <- eval_arith_expr nil ie;
            f <- find_val prog id;
            match args with
            | SumR el' =>
                Some (SumR (Fun_v id (Const_e (Z.of_nat i)) el'))
            | SumL args =>
                l_val <- f (Some i) args;
                Some (SumL (linearize_list_value l_val nil))
            end
    end
with simpl_expr_list (arch : architecture) (prog : prog_ctxt) (ctxt : context) (el : expr_list) : option expr_list :=
    match el with
    | Enil => Some Enil
    | ECons e tl =>
        e' <- eval_expr arch prog ctxt e;
        tl <- simpl_expr_list arch prog ctxt tl;
        match e' with
        | SumR e' => Some (ECons e' tl)
        | SumL v =>
            e' <- list_val_to_expr v;
            Some (ECons e' tl)
        end
    end
with eval_expr_list (arch : architecture) (prog : prog_ctxt) (ctxt : context) (el : expr_list) : option (Sum (list (@cst_or_int Z)) expr_list) :=
    match el with
    | Enil => Some (SumL nil)
    | ECons e tl =>
        v <- eval_expr arch prog ctxt e;
        match v with
        | SumR e' =>
            tl' <- simpl_expr_list arch prog ctxt tl;
            Some (SumR (ECons e' tl'))
        | SumL v =>
            tl <- eval_expr_list arch prog ctxt tl;
            match tl with
            | SumR tl' =>
                e' <- list_val_to_expr v;
                Some (SumR (ECons e' tl'))
            | SumL tl =>
                Some (SumL (linearize_list_value v tl))
            end
        end
    end
with eval_expr_list' (arch : architecture) (prog : prog_ctxt) (ctxt : context) (el : expr_list) : option (Sum (option (nat * list Z * list nat * dir)) expr_list) :=
    match el with
    | Enil => Some (SumL None)
    | ECons e tl =>
        v <- eval_expr arch prog ctxt e;
        match v with
        | SumR e' =>
            tl' <- simpl_expr_list arch prog ctxt tl;
            Some (SumR (ECons e' tl'))
        | SumL v =>
            tl <- eval_expr_list' arch prog ctxt tl;
            match tl with
            | SumR tl' =>
                e' <- list_val_to_expr v;
                Some (SumR (ECons e' tl'))
            | SumL tl =>
                match v with
                | CoIR d v form::nil =>
                    match tl with
                    | None => Some (SumL (Some (1, v, form, d)))
                    | Some (l, v', form', d') =>
                        if dir_beq d d' && list_beq nat Nat.eqb form form'
                        then
                            Some (SumL (Some (l + 1, v ++ v', form', d')))
                        else None
                    end
                | _ => None
                end
            end
        end
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

Fixpoint build_ctxt_aux (typ : typ) (input : list (@cst_or_int Z)) (l : list nat) : option (expr * list (@cst_or_int Z)) :=
    match typ with
    | Nat => match input with
        | CoIL n :: input' => Some (Const n (Some typ), input') 
        | _ => None
        end
    | Uint d (Mint n) =>
        annot <- IntSize_of_nat n;
        d' <- match d with
            | Hslice => Some (DirH annot)
            | Vslice => Some (DirV annot)
            | Bslice => Some DirB
            | _ => None
        end;
        (valL, input') <- build_ctxt_aux_take_n (prod_list l) input d';
        expr <- expr_of_val l (Uint d (Mint n)) valL;
        Some (expr, input')
    | Uint _ Mnat => None
    | Uint _ (Mvar _) => None
    | Array typ len =>
        build_ctxt_aux typ input (l ++ [:: len])
    end.

Fixpoint build_ctxt (args : p) (input : list (@cst_or_int Z)) : option (list (list var * expr)) :=
    match args with
    | nil => match input with
        | nil => Some nil
        | _::_ => None
        end
    | var::tl =>
        (expr, input') <- build_ctxt_aux (VD_TYP var) input nil;
        ctxt <- build_ctxt tl input';
        Some (([:: Var (VD_ID var)], expr)::ctxt)
    end.

Fixpoint update_context {A} (f : value_tree -> A -> option (value_tree * A))
    (v : ident) (ctxt : context) (a : A) : option (context * A) :=
    match ctxt with
    | nil => None
    | (v', (dir, tree)) :: tl =>
        if ident_beq v v'
        then
            (tree', a') <- f tree a;
            Some ((v', (dir, tree')) :: tl, a')
        else
            (tl', a') <- update_context f v tl a;
            Some ((v', (dir, tree)) :: tl', a')
    end
.

Fixpoint build_trees {A} (f : A -> option (value_tree * A)) (len : nat) (a : A) : option (list_value_tree * A) :=
    match len with
    | 0 => Some (LVTnil, a)
    | S len =>
        (hd, a') <- f a;
        (tl, a'') <- build_trees f len a';
        Some (LVTcons hd tl, a'')
    end
.

Fixpoint fill_tree (t : typ) (values : seq (@cst_or_int Z)) : option (value_tree * seq (@cst_or_int Z)) :=
    match t with
    | Nat => None
    | Uint d (Mint n) =>
        annot <- IntSize_of_nat n;
        d' <- match d with
            | Hslice => Some (DirH annot)
            | Vslice => Some (DirV annot)
            | Bslice => Some DirB
            | _ => None
        end;
        match build_ctxt_aux_take_n 1 values d' with
        | Some ([:: v], values') =>
            Some (VTBase (SumL v), values')
        | _ => None
        end
    | Uint _ Mnat => None
    | Uint _ (Mvar _) => None
    | Array typ len =>
        (trees, values') <- build_trees (fill_tree typ) len values;
        Some (VTRec trees, values')
    end
.

Fixpoint update_trees {A} (f : value_tree -> A -> option (value_tree * A)) (l : list_value_tree) (pos : nat) (a : A) : option (list_value_tree * A) :=
    match l with
    | LVTnil => None
    | LVTcons hd tl =>
        match pos with
        | 0 =>
            (hd', a') <- f hd a;
            Some (LVTcons hd' tl, a')
        | S pos =>
            (tl', a') <- update_trees f tl pos a;
            Some (LVTcons hd tl', a')
        end
    end.

Fixpoint gen_trees (t : value_tree) (len : nat) : list_value_tree :=
    match len with
    | 0 => LVTnil
    | S len => LVTcons t (gen_trees t len)
    end
.

Fixpoint update_value_tree (path : seq indexing) (tree : value_tree)
    (values : seq (@cst_or_int Z)) : option (value_tree * seq (@cst_or_int Z)) :=
    match path with
    | nil =>
        match tree with
        | VTRec _ => None
        | VTBase (SumL _) => None
        | VTBase (SumR typ) =>
            fill_tree typ values
        end
    | ind :: path_tl =>
        trees <- match tree with
        | VTBase (SumL _) => None
        | VTBase (SumR (Array typ len)) =>
            Some (gen_trees (VTBase (SumR typ)) len)
        | VTBase (SumR _typ) => None
        | VTRec trees => Some trees
        end;
        iL <- match ind with
            | IInd ae => option_map (fun i => [:: i]) (eval_arith_expr nil ae)
            | IRange ae1 ae2 =>
                i1 <- eval_arith_expr nil ae1;
                i2 <- eval_arith_expr nil ae2;
                Some (gen_range i1 i2)
            | ISlice aeL =>
                remove_option_from_list (map (eval_arith_expr nil) aeL)
        end;
        (trees', values') <- fold_left
            (fun opair i =>
                (trees, values) <- opair;
                update_trees (update_value_tree path_tl) trees i values)
            iL (Some (trees, values));
        Some (VTRec trees', values')
    end
.

Fixpoint bind_equation (vars : seq var) (values : seq (@cst_or_int Z)) (ctxt : context) : option context :=
    match vars with
    | nil =>
        match values with
        | nil => Some ctxt
        | _ :: _ => None
        end
    | var :: tl =>
        (ctxt', values') <- match var with
            | Var v => update_context (update_value_tree nil) v ctxt values
            | Index (Var v) ind =>
                update_context (update_value_tree ind) v ctxt values
            | Index (Index _ _ ) _ => None
        end;
        bind_equation tl values' ctxt'
    end
.

Fixpoint simplify_equations (arch : architecture) (prog : prog_ctxt) (ctxt : context) (eqns : list (list var * expr)) : option (context * list (list var * expr)) :=
    match eqns with
    | nil => Some (ctxt, eqns)
    | (vars, expr) :: tl =>
        v <- eval_expr arch prog ctxt expr;
        match v with
        | SumR expr' =>
            (ctxt', tl') <- simplify_equations arch prog ctxt tl;
            Some (ctxt', (vars, expr') :: tl')
        | SumL val =>
            ctxt' <- bind_equation vars val ctxt;
            simplify_equations arch prog ctxt' tl
        end
    end
.

Fixpoint simplify_equations_iters (arch : architecture) (prog : prog_ctxt) (fuel : nat) (ctxt : context) (eqns : list (list var * expr)) : option context :=
    match fuel with
    | 0 =>
        match eqns with
        | nil => Some ctxt
        | _ :: _ => None
        end
    | S fuel =>
        (ctxt', eqns') <- simplify_equations arch prog ctxt eqns;
        simplify_equations_iters arch prog fuel ctxt' eqns'
    end
.

Definition tree_of_p (arg : var_d) : option (ident * (dir * value_tree)) :=
    (dir, _) <- convert_type (VD_TYP arg); 
    Some (VD_ID arg, (dir, VTBase (SumR (VD_TYP arg)))).


Definition compute_result (ctxt : context) (v : var_d) : option (@cst_or_int Z) :=
    (dir, val) <- find_val ctxt (VD_ID v);
    match collect_all_value_tree val with
    | SumR tt => None
    | SumL (val, form) => Some (CoIR dir val form)
    end. 

Fixpoint eval_node_inner (arch : architecture) (prog : prog_ctxt) (in_names out_names : p)
        (def : def_i) (i : option nat) (input : list cst_or_int)
            : option (list cst_or_int) :=
    match def, i with
    | Single temp_vars eqns, None =>
        eqns <- list_of_list_deq nil eqns;
        args <- build_ctxt in_names input;
        let eqns := args ++ eqns in
        ctxt <- remove_option_from_list (map tree_of_p (in_names ++ temp_vars ++ out_names));
        ctxt' <- simplify_equations_iters arch prog (length eqns) ctxt eqns;
        remove_option_from_list (map (compute_result ctxt') out_names)
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
