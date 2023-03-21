From mathcomp Require Import all_ssreflect.

Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sets.Ensembles.

From Usuba Require Import usuba_AST.

Definition IntSize : Type := nat.
    (* | S1 | S8 | S16 | S32 | S64
    | S128 | S256 | S512. *)
(* Scheme Equality for IntSize. *)
Definition IntSize_beq := Nat.eqb.

(* Definition IntSize_of_nat (n : nat) : option IntSize :=
    if Nat.eqb n 1
    then Some S1
    else if Nat.eqb n 8
    then Some S8
    else if Nat.eqb n 16
    then Some S16
    else if Nat.eqb n 32
    then Some S32
    else if Nat.eqb n 64
    then Some S64
    else if Nat.eqb n 128
    then Some S128
    else if Nat.eqb n 256
    then Some S256
    else if Nat.eqb n 512
    then Some S512
    else None. *)
Definition IntSize_of_nat (n : nat) : option IntSize := Some n.

Inductive dir := DirH | DirV.
Scheme Equality for dir.

Inductive Value :=
    | VInt : dir -> list nat -> IntSize -> Value
    | VConst : nat -> Value
    | ValTuple : list_Value -> Value
with list_Value :=
    | lV_nil : list_Value
    | lV_cons : Value -> list_Value -> list_Value.

Record architecture : Type := {
    ARCH_ADD : IntSize -> dir -> option (nat -> nat -> nat);
    ARCH_SUB : IntSize -> dir -> option (nat -> nat -> nat);
    ARCH_DIV : IntSize -> dir -> option (nat -> nat -> nat);
    ARCH_MOD : IntSize -> dir -> option (nat -> nat -> nat);
    ARCH_MUL : IntSize -> dir -> option (nat -> nat -> nat);

    ARCH_NOT : IntSize -> dir -> option (nat -> nat);
    ARCH_AND : IntSize -> dir -> option (nat -> nat -> nat);
    ARCH_OR  : IntSize -> dir -> option (nat -> nat -> nat);
    ARCH_XOR : IntSize -> dir -> option (nat -> nat -> nat);
    ARCH_ANDN : IntSize -> dir -> option (nat -> nat -> nat);

    ARCH_LSHIFT : nat -> IntSize -> dir -> option (nat -> nat);
    ARCH_RSHIFT  : nat -> IntSize -> dir -> option (nat -> nat);
    ARCH_RASHIFT : nat -> IntSize -> dir -> option (nat -> nat);
    ARCH_LROTATE : nat -> IntSize -> dir -> option (nat -> nat);
    ARCH_RROTATE : nat -> IntSize -> dir -> option (nat -> nat);
}.

Definition context : Type := list (ident * Value).

Fixpoint find_val (ctxt : context) (i : ident) : option Value :=
    match ctxt  with
        | nil => None
        | ((name, val)::tl) =>
            if String.eqb i name
            then Some val
            else find_val tl i
    end.

Fixpoint find_const (ctxt : context) (var : ident) : option nat :=
    match ctxt  with
        | nil => None
        | ((name, v)::tl) =>
            if String.eqb var name
            then match v with
                | VConst i => Some i
                | _ => None
                end
            else find_const tl var
    end.

Notation " p <- e ; f " :=
    match (e : option _) return option _ with
        | Some x => (fun p => f) x
        | None => None
    end (at level 79, p as pattern, right associativity).

Fixpoint list_map2 {A B C : Type} (op : A -> B -> C) (l1 : list A) (l2 : list B) : option (list C) :=
    match l1, l2 with
    | nil, nil => Some nil
    | h1::t1, h2::t2 =>
        tl <- list_map2 op t1 t2;
        Some (op h1 h2::tl)
    | _, _ => None
    end.

Function eval_binop (binop : IntSize -> dir -> option (nat -> nat -> nat)) (v1 v2 : Value) : option Value :=
    match v1 with
        | VInt d1 i1 s1 =>
            match v2 with
                | VInt d2 i2 s2 =>
                    if IntSize_beq s1 s2 && dir_beq d1 d2
                    then
                        op <- binop s1 d1;
                        l <- list_map2 op i1 i2;
                        Some (VInt d1 l s1)
                    else None
                | _ => None
            end
        |  ValTuple t1 =>
            match v2 with
                |  ValTuple t2 =>
                    t <- eval_binop_tuples binop t1 t2; Some ( ValTuple t)
                | _ => None
            end
        | VConst _ => None
    end
with eval_binop_tuples (binop : IntSize -> dir -> option (nat -> nat -> nat)) (t1 t2 : list_Value) : option (list_Value) :=
    match t1 with
    | lV_nil => match t2 with
            | lV_nil => Some lV_nil
            | _ => None
        end
    | lV_cons h1 tl1 => match t2 with
        | lV_nil => None
        | lV_cons h2  tl2 =>
            s <- eval_binop binop h1 h2;
            tl <- eval_binop_tuples binop tl1 tl2;
            Some (lV_cons s tl)
        end
end.

Function eval_monop (monop : IntSize -> dir -> option (nat -> nat)) (v : Value) : option Value :=
    match v with
        | VInt d i s =>
            op <- monop s d;
            Some (VInt d (map op i) s)
        |  ValTuple t =>
            t <- eval_monop_tuples monop t; Some ( ValTuple t)
        | VConst _ => None
    end
with eval_monop_tuples (monop : IntSize -> dir -> option (nat -> nat)) (t : list_Value) : option (list_Value) :=
    match t with
    | lV_nil => Some lV_nil
    | lV_cons h tl =>
        s <- eval_monop monop h;
        tl <- eval_monop_tuples monop tl;
        Some (lV_cons s tl)
    end.

Fixpoint eval_arith_expr (ctxt : context) (e : arith_expr) : option nat :=
    match e with
        | Const_e i => Some i
        | Var_e var => find_const ctxt var
        | Op_e op e1 e2 =>
            v1 <- eval_arith_expr ctxt e1;
            v2 <- eval_arith_expr ctxt e2;
            match op with
                | Add => Some (v1 + v2)
                | Mul => Some (v1 * v2)
                | Sub => Some (v1 - v2)
                | Mod => Some (v1 mod v2)
                | Div => some (v1 / v2)
            end
    end.

Fixpoint get_val_in_l (i : nat) (l : list_Value) : option Value :=
    match l with
    | lV_nil => None
    | lV_cons hd tl =>
        match i with
        | 0 => Some hd
        | S i' => get_val_in_l i' l
        end
    end.

Fixpoint get_slice (l : list_Value) (indexes : list nat) : option (list_Value) :=
    match indexes with
    | nil => Some lV_nil
    | i::tl =>
        v <- get_val_in_l i l;
        tl <- get_slice l tl;
        Some (lV_cons v tl)
    end.

Fixpoint get_range (l : list_Value) (s e : nat) : option (list_Value) :=
    match e with
    | 0 => Some lV_nil
    | S e' => match l with
        | lV_nil => None
        | lV_cons v tl => match s with
            | 0 =>
                tl <- get_range tl 0 e';
                Some (lV_cons v tl)
            | S s' => get_range tl s' e'
            end
        end
    end.

Function eval_var (ctxt : context) (v : var) : option Value :=
    match v with
    | Var v => find_val ctxt v
    | VTuple vL =>
        valL <- eval_vars ctxt vL;
        Some (ValTuple valL)
    | Index v ae =>
        i <- eval_arith_expr ctxt ae;
        val <- eval_var ctxt v;
        match val with
        | ValTuple l => get_val_in_l i l
        | _ => None
        end
    | Range v ae1 ae2 =>
        i1 <- eval_arith_expr ctxt ae1;
        i2 <- eval_arith_expr ctxt ae2;
        val <- eval_var ctxt v;
        match val with
        | ValTuple l =>
            range <- get_range l i1 i2; Some (ValTuple range)
        | _ => None
        end
    | Slice v ael =>
        il <- fold_right (fun ae l =>
            l' <- l; i <- eval_arith_expr ctxt ae; Some (i::l')) (Some nil) ael;
        val <- eval_var ctxt v;
        match val with
        | ValTuple l =>
            slice <- get_slice l il; Some (ValTuple slice)
        | _ => None
        end
    end
with eval_vars ctxt vL :=
    match vL with
    | LVnil => Some lV_nil
    | LVcons v vL =>
        v <- eval_var ctxt v;
        vL <- eval_vars ctxt vL;
        Some (lV_cons v vL)
    end.

Function loop_rec (ctxt : context) (iter : context -> option context) i (s_i e_i : nat) : option context :=
    match e_i with
    | 0 => Some ctxt
    | S e_i' =>
        if (Nat.leb e_i s_i)
        then Some ctxt
        else
            ctxt' <- loop_rec ctxt iter i s_i e_i';
            iter ((i, VConst e_i')::ctxt')
    end.

Fixpoint replace_id (i : nat) (l : list_Value) (v : Value) : option list_Value :=
    match l with
    | lV_nil => None
    | lV_cons hd tl => match i with
        | 0 => Some (lV_cons v tl)
        | S i' =>
            tl' <- replace_id i' tl v;
            Some (lV_cons hd tl')
        end
    end.

Function bind (ctxt : context) v e :=
    match v with
    | VTuple vl => match e with
        | ValTuple el => bind_list ctxt vl el
        | _ => None
        end
    | Var v => Some ((v, e)::ctxt)
    | Index (Var var) ae =>
        i <- eval_arith_expr ctxt ae;
        match find_val ctxt var with
        | Some (ValTuple valL) =>
            valL' <- replace_id i valL e;
            Some ((var, ValTuple valL')::ctxt)
        | _ => None
        end
    | _ => None
    end
with bind_list ctxt vl el :=
    match vl with
    | LVnil => match el with
        | lV_nil => Some ctxt
        | _ => None
        end
    | LVcons v vl' => match el with
        | lV_cons e el' =>
            ctxt' <- bind ctxt v e;
            bind_list ctxt' vl' el'
        | _ => None
        end
    end.

Fixpoint extract_ctxt (var_names : p) (ctxt : context) : option (list Value) :=
    match var_names with
    | nil => Some nil
    | v::tl =>
        val <- find_val ctxt (VD_ID v);
        tl <- extract_ctxt tl ctxt;
        Some (val::tl)
    end.

Fixpoint list_of_list_Value (vL : list_Value) : list Value :=
    match vL with
    | lV_nil => nil
    | lV_cons h tl => h::list_of_list_Value tl
    end.

Fixpoint list_Value_of_list (vL : list Value) : list_Value :=
    match vL with
    | nil => lV_nil
    | h::tl => lV_cons h (list_Value_of_list tl)
    end.

Definition node_sem_type := option nat -> list Value -> option (list Value).
Definition prog_ctxt := list (ident * node_sem_type).

Fixpoint get_node (prog : prog_ctxt) (id : ident) : option node_sem_type :=
    match prog with
    | nil => None
    | (name, f) :: tl => if String.eqb name id
        then Some f
        else get_node tl id
    end.

Fixpoint build_int (n : nat) (len : nat) (size : nat) : list nat :=
    match len with
    | 0 => nil
    | S len' =>
        (n mod (2 ^ size))::build_int (n / (2 ^ size)) len' size
    end.

Definition build_integer (typ : typ) (n : nat) : option Value :=
    match typ with
    | Nat => None
    | Uint Hslice (Mint size) len =>
        annot <- IntSize_of_nat size;
        Some (VInt DirH (build_int n len size) annot)
    | Uint Vslice (Mint size) len =>
        annot <- IntSize_of_nat size;
        Some (VInt DirV (build_int n len size) annot)
    | Uint _ (Mint size) len => None
    | Uint _ Mnat _ => None
    | Uint _ (Mvar _) len => None
    | Array _ len => None
    end.

Function eval_expr (arch : architecture) (prog : prog_ctxt) (ctxt : context) (e : expr) : option Value :=
    match e with
        | Const n None => Some (VConst n)
        | Const n (Some typ) => build_integer typ n
        | ExpVar var => eval_var ctxt var
        | Tuple el => el <- eval_expr_list arch prog ctxt el; Some ( ValTuple el)
        | Not e =>
            v <- eval_expr arch prog ctxt e;
            eval_monop (ARCH_NOT arch) v
        | Log op e1 e2 =>
            v1 <- eval_expr arch prog ctxt e1;
            v2 <- eval_expr arch prog ctxt e2;
            f <- match op with
                | And => Some (ARCH_AND arch)
                | Or => Some (ARCH_OR arch)
                | Xor => Some (ARCH_XOR arch)
                | Andn => Some (ARCH_ANDN arch)
                | Masked _ => None
            end;
            eval_binop f v1 v2
        | Arith op e1 e2 =>
            v1 <- eval_expr arch prog ctxt e1;
            v2 <- eval_expr arch prog ctxt e2;
            let f := match op with
                | Add => ARCH_ADD arch
                | Sub => ARCH_SUB arch
                | Div => ARCH_DIV arch
                | Mod => ARCH_MOD arch
                | Mul => ARCH_MUL arch
            end
            in eval_binop f v1 v2
        | Shift op e1 e2 =>
            v1 <- eval_expr arch prog ctxt e1;
            v2 <- eval_arith_expr ctxt e2;
            let f := match op with
                | Lshift => ARCH_LSHIFT arch
                | Rshift => ARCH_RSHIFT arch
                | RAshift => ARCH_RASHIFT arch
                | Lrotate => ARCH_LROTATE arch
                | Rrotate => ARCH_RROTATE arch
                end
            in eval_monop (f v2) v1
        | Shuffle v l => None
        | Bitmask e ae => None
        | Pack e1 e2 None => None
        | Pack e1 e2 (Some t) => None
        | Fun id el =>
            args <- eval_expr_list arch prog ctxt el;
            f <- get_node prog id;
            l_val <- f None (list_of_list_Value args);
            Some (ValTuple (list_Value_of_list l_val))
        | Fun_v id ie el =>
            args <- eval_expr_list arch prog ctxt el;
            i <- eval_arith_expr ctxt ie;
            f <- get_node prog id;
            l_val <- f (Some i) (list_of_list_Value args);
            Some (ValTuple (list_Value_of_list l_val))
    end
with eval_expr_list (arch : architecture) (prog : prog_ctxt) (ctxt : context) (el : expr_list) : option list_Value :=
    match el with
    | Enil => Some lV_nil
    | ECons e tl =>
        v <- eval_expr arch prog ctxt e;
        tl <- eval_expr_list arch prog ctxt tl;
        Some (lV_cons v tl)
    end.

Function eval_deq (arch : architecture) (prog : prog_ctxt) (ctxt : context) (d : deq) : option context :=
    match d with
    | Eqn v e b =>
        e <- eval_expr arch prog ctxt e;
        bind ctxt v e
    | Loop i start_e end_e d2 opt =>
        start_i <- eval_arith_expr ctxt start_e;
        end_i <- eval_arith_expr ctxt end_e;
        ctxt' <- loop_rec ctxt (fun ctxt => eval_deq_list arch prog ctxt d2) i start_i end_i;
        match find_val ctxt i with
        | None => Some ctxt'
        | Some v => Some ((i, v)::ctxt')
        end
    end
with eval_deq_list (arch : architecture) (prog : prog_ctxt) (ctxt : context) (dl : list_deq) : option context :=
    match dl with
    | Dnil => Some ctxt
    | Dcons d dl' =>
        ctxt' <- eval_deq arch prog ctxt d;
        eval_deq_list arch prog ctxt' dl'
    end.

(* TODO *)

Inductive cst_or_int :=
    | CoIL : nat -> cst_or_int
    | CoIR : dir -> IntSize -> list nat -> cst_or_int.

Function flatten_value (val : Value) (l : list cst_or_int) : list cst_or_int :=
    match val with
    | VConst n => CoIL n::l
    | ValTuple vL => flatten_valueL vL l
    | VInt d n s => CoIR d s n::l
    end
with flatten_valueL (val : list_Value) (l : list cst_or_int) : list cst_or_int :=
    match val with
    | lV_nil => l
    | lV_cons hd tl =>
        flatten_value hd (flatten_valueL tl l)
    end.

Fixpoint build_ctxt_aux_take_n (nb : nat) (input : list cst_or_int) (d : dir) (annot : IntSize) : option (list_Value * list cst_or_int) :=
    match nb with
    | 0 => Some (lV_nil, input)
    | S nb' => match input with
        | nil => None
        | (CoIL n)::tl => None
        | (CoIR d s n)::tl =>
            if IntSize_beq s annot
            then
                (valTL, input') <- build_ctxt_aux_take_n nb' tl d annot;
                Some (lV_cons (VInt d n annot) valTL, input')
            else None
        end
    end.

Fixpoint build_ctxt_aux (typ : typ) (input : list cst_or_int) : option (Value * list cst_or_int) :=
    match typ with
    | Nat => None
    | Uint d (Mint n) nb =>
        annot <- IntSize_of_nat n;
        d <- match d with
            | Hslice => Some DirH
            | Vslice => Some DirV
            | _ => None
        end;
        (valL, input') <- build_ctxt_aux_take_n nb input d annot;
        Some (ValTuple valL, input')
    | Uint _ Mnat nb => None
    | Uint _ (Mvar _) nb => None
    | Array typ (Const_e len) =>
        let fix build_array len input :=
            match len with
            | 0 => Some (lV_nil, input)
            | S len' => 
                (valHD, input') <- build_ctxt_aux typ input;
                (valTL, input'') <- build_array len' input';
                Some (lV_cons valHD valTL, input'')
            end in
        (valL, input') <- build_array len input;
        Some (ValTuple valL, input')
    | Array _ _ => None
    end.

Fixpoint build_ctxt (args : p) (input : list cst_or_int) : option context :=
    match args with
    | nil => Some nil
    | var::tl =>
        (val, input') <- build_ctxt_aux (VD_TYP var) input;
        ctxt <- build_ctxt tl input';
        Some ((VD_ID var, val)::ctxt)
    end.


Fixpoint eval_node_inner (arch : architecture) (prog : prog_ctxt) (in_names out_names : p) (def : def_i) (i : option nat) (input : list Value) :=
    match def, i with
    | Single temp_vars eqns, None =>
        ctxt <- build_ctxt in_names (flatten_valueL (list_Value_of_list input) nil);
        ctxt' <- eval_deq_list arch prog ctxt eqns;
        extract_ctxt out_names ctxt'
    | Table l, None => match input with
        | (VConst i)::nil | VInt _ (i::nil) 1::nil =>
            i' <- nth_error l i;
            Some (VConst i'::nil)
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

Definition eval_node (node : def) (arch : architecture) (prog : prog_ctxt) : node_sem_type :=
    fun opt input =>
        eval_node_inner arch prog (P_IN node) (P_OUT node) (NODE node) opt input.
    

Fixpoint eval_prog (arch : architecture) (fprog : prog) : prog_ctxt :=
    match fprog with
    | nil => nil
    | node::prog =>
        let tl := eval_prog arch prog in
        (ID node, eval_node node arch tl)::tl
    end.

    
(* Freevars *)
    
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

Function var_freevars (v : var) : Ensemble ident :=
    match v with
    | Var var => Singleton ident var
    | Index v i => Union ident (var_freevars v) (aexpr_freevars i)
    | Range v s e => Union ident (var_freevars v) (Union ident (aexpr_freevars s) (aexpr_freevars e))
    | Slice v el => Union ident (var_freevars v) (aexprl_freevars el)
    | VTuple vl => varl_freevars vl
    end
with varl_freevars vl :=
    match vl with
    | LVnil => Empty_set ident
    | LVcons v tl => Union ident (var_freevars v) (varl_freevars tl)
    end.

Function expr_freevars (e : expr) : Ensemble ident :=
    match e with
    | Const _ _ => Empty_set ident
    | ExpVar v => var_freevars v
    | Tuple el => exprl_freevars el
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

Function deq_vars (d : deq) : Ensemble ident :=
    match d with 
    | Eqn v e _ => Union ident (expr_freevars e) (var_freevars v)
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

Function deq_boundvars (d : deq) : Ensemble ident :=
    match d with 
    | Eqn v e _ => (var_freevars v)
    | Loop i _ _ eqns _ => Union ident (Singleton ident i) (deqs_boundvars eqns)
    end
with deqs_boundvars (d : list_deq) : Ensemble ident :=
    match d with
    | Dnil => Empty_set ident
    | Dcons hd tl => Union ident (deq_boundvars hd) (deqs_boundvars tl)
    end.
