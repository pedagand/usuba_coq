(* Require Import Lia. *)
Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import seq ssrnat.
(* From mathcomp Require Import all_ssreflect. *)

From Usuba Require Import ident usuba_AST arch semantic_base.

(** We assert that `length values = prod_list dim` *)
Fixpoint get_access (values : list (option Z)) (acc : access) (dim : list nat) : option (list (option Z) * list nat) :=
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

Fixpoint eval_var_inner (v : var) (ctxt : context) : option (@cst_or_int (option Z)) :=
    match v with
    | Var v => find_val ctxt v
    | Index v ind =>
        acc <- access_of_ind ctxt ind;
        match eval_var_inner v ctxt with
        | Some (CoIR d values form) => 
            (values, form') <- get_access values acc form;
            Some (CoIR d values form')
        | _ => None
        end
    end.

Definition eval_var (v : var) (ctxt : context) : option (@cst_or_int Z) :=
    match eval_var_inner v ctxt with
    | Some (CoIL l) => Some (CoIL l)
    | Some (CoIR d values form) =>
        values' <- remove_option_from_list values;
        Some (CoIR d values' form)
    | None => None
    end.

Fixpoint loop_rec (ctxt : context) (iter : context -> option context) i (s_i e_i : nat) : option context :=
    if (Nat.ltb e_i s_i)
    then Some ctxt
    else
        match e_i with
        | 0 => iter ((i, CoIL (Z.of_nat e_i))::ctxt)
        | S e_i' =>
            ctxt' <- loop_rec ctxt iter i s_i e_i';
            iter ((i, CoIL (Z.of_nat e_i))::ctxt')
    end.

Fixpoint replace_id {A : Type} (i : nat) (l : list A) (v : A) : option (list A) :=
    match l with
    | nil => None
    | hd :: tl => match i with
        | 0 => Some (v :: tl)
        | S i' =>
            tl' <- replace_id i' tl v;
            Some (hd :: tl')
        end
    end.

Fixpoint extract_ctxt (var_names : p) (ctxt : context) : option (list (@cst_or_int Z)) :=
    match var_names with
    | nil => Some nil
    | v::tl =>
        match find_val ctxt (VD_ID v) with
        | None => None
        | Some (CoIL c) =>
            tl <- extract_ctxt tl ctxt;
            Some (linearize_list_value (CoIL c::nil) tl)
        | Some (CoIR d l form) =>
            l' <- remove_option_from_list l;
            tl <- extract_ctxt tl ctxt;
            Some (linearize_list_value (CoIR d l' form::nil) tl)
        end
    end.

Fixpoint eval_expr (arch : architecture) (prog : prog_ctxt) (ctxt : context) (e : expr) : option (list (@cst_or_int Z)) :=
    match e with
        | Const n None => Some (CoIL n::nil)
        | Const n (Some typ) => build_integer typ n
        | ExpVar var =>
            v <- eval_var var ctxt;
            Some [:: v]
        | BuildArray el => 
            o <- eval_expr_list' arch prog ctxt el;
            (len, values, form, d) <- o;
            Some [:: CoIR d values (len::form)]
        | Tuple el => eval_expr_list arch prog ctxt el
        | Not e =>
            v <- eval_expr arch prog ctxt e;
            eval_monop (arith_wrapper (IMPL_LOG arch) lnot) v
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
            eval_binop f v1 v2
        | Arith op e1 e2 =>
            v1 <- eval_expr arch prog ctxt e1;
            v2 <- eval_expr arch prog ctxt e2;
            let f := match op with
                | Add => arith_wrapper (IMPL_ARITH arch) add_fun
                | Sub => arith_wrapper (IMPL_ARITH arch) sub_fun
                | Div => arith_wrapper (IMPL_ARITH arch) div_fun
                | Mod => arith_wrapper (IMPL_ARITH arch) mod_fun
                | Mul => arith_wrapper (IMPL_ARITH arch) mul_fun
            end
            in eval_binop f v1 v2
        | Shift op e1 e2 =>
            v1 <- eval_expr arch prog ctxt e1;
            v2 <- eval_arith_expr ctxt e2;
            eval_shift arch op v1 v2
        | Shuffle v l => None
        | Bitmask e ae => None
        | Pack e1 e2 None => None
        | Pack e1 e2 (Some t) => None
        | Fun id el =>
            args <- eval_expr_list arch prog ctxt el;
            f <- find_val prog id;
            l_val <- f None args;
            Some (linearize_list_value l_val nil)
        | Fun_v id ie el =>
            args <- eval_expr_list arch prog ctxt el;
            i <- eval_arith_expr ctxt ie;
            f <- find_val prog id;
            l_val <- f (Some i) args;
            Some (linearize_list_value l_val nil)
    end
with eval_expr_list (arch : architecture) (prog : prog_ctxt) (ctxt : context) (el : expr_list) : option (list (@cst_or_int Z)) :=
    match el with
    | Enil => Some nil
    | ECons e tl =>
        v <- eval_expr arch prog ctxt e;
        tl <- eval_expr_list arch prog ctxt tl;
        Some (linearize_list_value v tl)
    end
with eval_expr_list' (arch : architecture) (prog : prog_ctxt) (ctxt : context) (el : expr_list) : option (option (nat * list Z * list nat * dir)) :=
    match el with
    | Enil => Some None
    | ECons e tl =>
        v <- eval_expr arch prog ctxt e;
        tl <- eval_expr_list' arch prog ctxt tl;
        match v with
        | CoIR d v form::nil =>
            match tl with
            | None => Some (Some (1, v, form, d))
            | Some (l, v', form', d') =>
                if dir_beq d d' && list_beq nat Nat.eqb form form'
                then
                    Some (Some (l + 1, v ++ v', form', d'))
                else None
            end
        | _ => None
        end
    end.

Fixpoint update_ind {A : Type} (i : nat) (l : list A) (v : A) : option (list A) :=
    match l with
    | nil => None
    | hd::tl => match i with
        | 0 => Some (v::tl)
        | S i' =>
            tl' <- update_ind i' tl v;
            Some (hd::tl')
        end
    end.

(*
    test if
    b = false \=> Forall is_none l
    b = true \=> Forall is_some l
*)
Fixpoint can_bind {A : Type} (l : list (option A)) (b : bool) : bool :=
    match l with
    | nil => true
    | None::tl => (negb b) && can_bind tl b
    | Some _::tl => b && can_bind tl b
    end.

(* We assert that `prod_list form = length val` *)
Fixpoint update (form : list nat) (val : list (option Z)) (acc : access) (e : list (@cst_or_int Z)) (dir : dir) (b : bool) : option (list (option Z) * list (@cst_or_int Z)) :=
    match form with
    | nil => match acc with
        | AAll =>
            if can_bind val b
            then
                (l1, l2) <- build_ctxt_aux_take_n (length val) e dir;
                Some (map Some l1, l2)
            else
                None
        | _ => None
        end
    | form_hd::form_tl =>
        if length val mod form_hd =? 0
        then
            val' <- split_into_segments form_hd (prod_list form_tl) val;
            match acc with
            | AAll =>
                (l1, l2) <- build_ctxt_aux_take_n (length val) e dir;
                Some (map Some l1, l2)
            | AInd i acc_tl =>
                subl <- nth_error val' i;
                (subl', e') <- update form_tl subl acc_tl e dir b;
                val'' <- update_ind i val' subl';
                Some (concat val'', e')
            | ASlice iL acc_tl =>
                (val'', e') <- fold_left (fun state i =>
                                    (val', e) <- state;
                                    subl <- nth_error val' i;
                                    (subl', e') <- update form_tl subl acc_tl e dir b;
                                    val'' <- update_ind i val' subl';
                                    Some (val'', e')) iL (Some (val', e));
                Some (concat val'', e')
            end
        else None
    end.

Definition bind_aux (ctxt : context) (type_ctxt : type_ctxt) (v : bvar) (e : list (@cst_or_int Z)) (b : bool) : option (context * list (@cst_or_int Z)) :=
    let (v, ind) := v in
    typ <- find_val type_ctxt v;
    (dir, form) <- convert_type typ;
    let val_init := match find_val ctxt v with
    | None => undefined (prod_list form)
    | Some (CoIL i) => Some i::nil
    | Some (CoIR _ iL _) => iL
    end in
    acc <- access_of_ind ctxt ind;
    (val, e') <- update form val_init acc e dir b;
    Some ((v, CoIR dir val form)::ctxt, e')
.

Fixpoint bind_aux_list ctxt type_ctxt (vl : list bvar) (el : list (@cst_or_int Z)) (b : bool) : option (context * list (@cst_or_int Z)) :=
    match vl with
    | nil => match el with
        | nil => Some (ctxt, el)
        | _ => None
        end
    | v :: vl' =>
        (ctxt', el') <- bind_aux ctxt type_ctxt v el b;
        bind_aux_list ctxt' type_ctxt vl' el' b
    end.

Definition bind ctxt type_ctxt (vl : list bvar) (el : list (@cst_or_int Z)) (b : bool) : option context :=
    match bind_aux_list ctxt type_ctxt vl el b with
    | Some (ctxt', nil) => Some ctxt'
    | _ => None
    end. 

Fixpoint eval_deq (arch : architecture) (prog : prog_ctxt) (type_ctxt : type_ctxt) (ctxt : context) (d : deq) : option context :=
    match d with
    | Eqn v e b =>
        e <- eval_expr arch prog ctxt e;
        bind ctxt type_ctxt v e b
    | Loop i start_e end_e d2 opt =>
        start_i <- eval_arith_expr ctxt start_e;
        end_i <- eval_arith_expr ctxt end_e;
        ctxt' <- loop_rec ctxt (fun ctxt => eval_deq_list arch prog type_ctxt ctxt d2) i start_i end_i;
        match find_val ctxt i with
        | None => Some ctxt'
        | Some v => Some ((i, v)::ctxt')
        end
    end
with eval_deq_list (arch : architecture) (prog : prog_ctxt) (type_ctxt : type_ctxt) (ctxt : context) (dl : list_deq) : option context :=
    match dl with
    | Dnil => Some ctxt
    | Dcons d dl' =>
        ctxt' <- eval_deq arch prog type_ctxt ctxt d;
        eval_deq_list arch prog type_ctxt ctxt' dl'
    end.

Fixpoint build_type_ctxt (l : p) : type_ctxt :=
    match l with
    | nil => nil
    | hd::tl => (VD_ID hd, VD_TYP hd) :: build_type_ctxt tl
    end.

Fixpoint build_ctxt_aux (typ : typ) (input : list (@cst_or_int Z)) (l : list nat) : option (@cst_or_int (option Z) * list (@cst_or_int Z)) :=
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
        Some (CoIR d (map Some valL) l, input')
    | Uint _ Mnat => None
    | Uint _ (Mvar _) => None
    | Array typ len =>
        build_ctxt_aux typ input (l ++ [:: len])
    end.

Fixpoint build_ctxt (args : p) (input : list (@cst_or_int Z)) : option context:=
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

Fixpoint eval_node_inner (arch : architecture) (prog : prog_ctxt) (in_names out_names : p) (def : def_i) (i : option nat) (input : list (@cst_or_int Z)) : option (list (@cst_or_int Z)) :=
    match def, i with
    | Single temp_vars eqns, None =>
        ctxt <- build_ctxt in_names input;
        ctxt' <- eval_deq_list arch prog (build_type_ctxt (temp_vars ++ in_names ++ out_names)) ctxt eqns;
        extract_ctxt out_names ctxt'
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
