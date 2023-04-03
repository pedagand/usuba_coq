Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import usuba_AST.

Definition IntSize : Type := nat.
Definition IntSize_beq := Nat.eqb.

Definition IntSize_of_nat (n : nat) : option IntSize := Some n.

Inductive dir :=
    | DirH of IntSize
    | DirV of IntSize
    | DirB.
Scheme Equality for dir.

Inductive cst_or_int {A : Type} :=
    | CoIL : nat -> cst_or_int
    | CoIR : dir -> list A -> option (list nat) -> cst_or_int.
Scheme Equality for option.
Scheme Equality for list.

Definition Value := list (@cst_or_int nat).

Record architecture : Type := {
    ARCH_ADD : dir -> option (nat -> nat -> nat);
    ARCH_SUB : dir -> option (nat -> nat -> nat);
    ARCH_DIV : dir -> option (nat -> nat -> nat);
    ARCH_MOD : dir -> option (nat -> nat -> nat);
    ARCH_MUL : dir -> option (nat -> nat -> nat);

    ARCH_NOT : dir -> option (nat -> nat);
    ARCH_AND : dir -> option (nat -> nat -> nat);
    ARCH_OR  : dir -> option (nat -> nat -> nat);
    ARCH_XOR : dir -> option (nat -> nat -> nat);
    ARCH_ANDN : dir -> option (nat -> nat -> nat);

    ARCH_LSHIFT : nat -> dir -> option (nat -> nat);
    ARCH_RSHIFT  : nat -> dir -> option (nat -> nat);
    ARCH_RASHIFT : nat -> dir -> option (nat -> nat);
    ARCH_LROTATE : nat -> dir -> option (nat -> nat);
    ARCH_RROTATE : nat -> dir -> option (nat -> nat);
}.

Definition context : Type := list (ident * @cst_or_int (option nat)).

Fixpoint find_val {A : Type} (ctxt : list (ident * A)) (i : ident) : option A :=
    match ctxt with
        | nil => None
        | ((name, val)::tl) =>
            if String.eqb i name
            then Some val
            else find_val tl i
    end.

Fixpoint find_node (p : prog) (i : ident) : option def :=
    match p with
        | nil => None
        | node::tl =>
            if String.eqb i (ID node)
            then Some node
            else find_node tl i
    end.

Fixpoint find_const (ctxt : context) (var : ident) : option nat :=
    match ctxt with
        | nil => None
        | ((name, v)::tl) =>
            if String.eqb var name
            then match v with
                | CoIL i => Some i
                | _ => None
                end
            else find_const tl var
    end.

Fixpoint list_map2 {A B C : Type} (op : A -> B -> C) (l1 : list A) (l2 : list B) : option (list C) :=
    match l1, l2 with
    | nil, nil => Some nil
    | h1::t1, h2::t2 =>
        tl <- list_map2 op t1 t2;
        Some (op h1 h2::tl)
    | _, _ => None
    end.

Definition eval_binop_coi (binop : dir -> option (nat -> nat -> nat)) (v1 v2 : @cst_or_int nat) : option (@cst_or_int nat) :=
    match v1 with
    | CoIL i => None
    | CoIR d1 i1 l1 =>
        match v2 with
        | CoIL i2 => None
        | CoIR d2 i2 l2 =>
            if dir_beq d1 d2
            then
                op <- binop d1;
                l <- list_map2 op i1 i2;
                Some (CoIR d1 l None)
            else None
        end
    end.

Fixpoint eval_binop (binop : dir -> option (nat -> nat -> nat)) (l1 l2 : list (@cst_or_int nat)) : option (list (@cst_or_int nat)) :=
    match l1 with
    | nil => match l2 with
        | nil => Some nil
        | _::_ => None
        end
    | h1::tl1 => match l2 with
        | nil => None
        | h2::tl2 =>
            hd <- eval_binop_coi binop h1 h2;
            tl <- eval_binop binop tl1 tl2;
            Some (hd :: tl)
        end
    end.

Definition eval_monop_coi (monop : dir -> option (nat -> nat)) (v : @cst_or_int nat) : option (@cst_or_int nat) :=
    match v with
    | CoIL _ => None
    | CoIR d i l => 
        op <- monop d;
        Some (CoIR d (map op i) l)
    end.

Fixpoint eval_monop (monop : dir -> option (nat -> nat)) (v : list (@cst_or_int nat)) : option (list (@cst_or_int nat)) :=
    match v with
    | nil => Some nil
    | hd::tl =>
        hd' <- eval_monop_coi monop hd;
        tl' <- eval_monop monop tl;
        Some (hd' :: tl')
    end.

(* Fixpoint repeat_value (nb : nat) (zero : Value) : list_Value :=
    match nb with
    | 0 => lV_nil
    | S nb' => lV_cons zero (repeat_value nb' zero)
    end. *)

(* Function zero_from_val (v : Value) : Value :=
    match v with
    | VConst n => VConst 0
    | VInt d n l => VInt d (map (fun _ => 0) n) l
    | VTuple l => VTuple (zero_from_valL l)
    end
with zero_from_valL l :=
    match l with
    | lV_nil => lV_nil
    | lV_cons hd tl => lV_cons (zero_from_val hd) (zero_from_valL tl)
    end. *)

(* Definition zero_from (t : list_Value) : option Value :=
    match t with
    | lV_nil => None
    | lV_cons hd _ => Some (zero_from_val hd)
    end. *)


Fixpoint take_n {A : Type} (nb : nat) (l : list A) : option (list A * list A) :=
    match nb with
    | 0 => Some (nil, l)
    | S nb' => match l with
        | nil => None
        | hd :: tl =>
            (s, e) <- take_n nb' tl;
            Some (hd :: s, e)
        end
    end.


Definition eval_shift (op : shift_op) (arch : architecture) (v : list (@cst_or_int nat)) (v2 : nat) : option (list (@cst_or_int nat)) :=
    match v with
    | CoIR d (i::nil) len::nil =>
        f <- match op with
            | Lshift => ARCH_LSHIFT arch v2 d
            | Rshift => ARCH_RSHIFT arch v2 d
            | RAshift => ARCH_RASHIFT arch v2 d
            | Lrotate => ARCH_LROTATE arch v2 d
            | Rrotate => ARCH_RROTATE arch v2 d
            end;
        Some (CoIR d (f i::nil) len::nil)
    | CoIR d i len::nil => match op with
        | Lshift =>
            (hd, tl) <- take_n v2 i;
            Some (CoIR d (app tl (map (fun => 0) hd)) len::nil)
        | _ => None
        end
    | _ => None
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

Inductive access : Type :=
    | AAll : access
    | ASlice : list nat -> access -> access.

Fixpoint split_into_segments {A : Type} (nb_segments segment_size : nat) (l : list A) : option (list (list A)) :=
    match nb_segments with
    | 0 => match l with
        | nil => Some nil
        | _ => None
        end
    | S nb_segments' =>
        (hd, tl) <- take_n segment_size l;
        tl' <- split_into_segments nb_segments' segment_size tl;
        Some (hd::tl')
    end.

Fixpoint remove_option_from_list {A : Type} (l : list (option A)) : option (list A) :=
    match l with
    | nil => Some nil
    | hd::tl =>
        hd' <- hd;
        tl' <- remove_option_from_list tl;
        Some (hd'::tl')
    end.

(** We assert that `length values = prod_list dim` *)
Fixpoint get_access (values : list (option nat)) (acc : access) (dim : list nat) : option (list nat) :=
    match dim with
    | nil =>
        match values with
        | n::nil =>
            match acc with
            | AAll => remove_option_from_list values
            | ASlice indices tl =>
                if forallb (fun x => x =? 0) indices
                then
                    l <- get_access values tl nil;
                    Some (flat_map (fun _ => l) indices)
                else
                    None
            end
        | _ => None (** Assertion not verified *)
        end
    | d::dim_tl =>
        if length values mod d =? 0
        then
            l' <- split_into_segments d (length values / d) values;
            match acc with
            | AAll => remove_option_from_list values
            | ASlice indices acc_tl =>
                fold_right (fun v l => l' <- l; v' <- v; v'' <- get_access v' acc_tl dim_tl; Some (v'' ++ l'))
                                (Some nil) (map (fun i => nth_error l' i) indices) 
            end
        else None (** Assertion not verified *)
    end.

Fixpoint gen_range_incr (i1 i2 : nat) : list nat :=
    if i1 <? i2
    then nil
    else
        match i2 with
        | 0 => nil
        | S i2' => gen_range_incr i1 i2'
        end ++ i2::nil.

Fixpoint gen_range_decr (i1 i2 : nat) : list nat :=
    if i1 <? i2
    then nil
    else
        i1::match i1 with
        | 0 => nil
        | S i1' => gen_range_decr i1' i2
        end.

Definition gen_range (i1 i2 : nat) : list nat :=
    if i1 <=? i2
    then gen_range_incr i1 i2
    else gen_range_decr i1 i2.

Fixpoint eval_var (ctxt : context) (v : var) (acc : access) : option (list (@cst_or_int nat)) :=
    match v with
    | Var v => 
        val <- find_val ctxt v;
        match val, acc with
        | CoIR _ _ None, _ => None
        | CoIL cst, _ =>
            iL' <- get_access (Some cst::nil) acc nil;
            Some (map CoIL iL')
        | CoIR dir iL (Some dim), _ =>
            iL' <- get_access iL acc dim;
            Some ((CoIR dir iL' None)::nil)
        end
    | Index v ae =>
        i <- eval_arith_expr ctxt ae;
        eval_var ctxt v (ASlice [:: i] acc)
    | Range v ae1 ae2 =>
        i1 <- eval_arith_expr ctxt ae1;
        i2 <- eval_arith_expr ctxt ae2;
        eval_var ctxt v (ASlice (gen_range i1 i2) acc)
    | Slice v ael =>
        il <- fold_right (fun ae l =>
            l' <- l; i <- eval_arith_expr ctxt ae; Some (i::l')) (Some nil) ael;
        eval_var ctxt v (ASlice il acc)
    end.

Function loop_rec (ctxt : context) (iter : context -> option context) i (s_i e_i : nat) : option context :=
    match e_i with
    | 0 => Some ctxt
    | S e_i' =>
        if (Nat.leb e_i s_i)
        then Some ctxt
        else
            ctxt' <- loop_rec ctxt iter i s_i e_i';
            iter ((i, CoIL e_i')::ctxt')
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

Definition type_ctxt : Type := list (ident * typ).

Definition node_sem_type := option nat -> list (@cst_or_int nat) -> option (list (@cst_or_int nat)).
Definition prog_ctxt := list (ident * node_sem_type).

Fixpoint get_node (prog : prog_ctxt) (id : ident) : option node_sem_type :=
    match prog with
    | nil => None
    | (name, f) :: tl => if String.eqb name id
        then Some f
        else get_node tl id
    end.

Definition build_integer (typ : typ) (n : nat) : option (list (@cst_or_int nat)) :=
    match typ with
    | Nat => Some (CoIL n::nil)
    | Uint Hslice (Mint size) 1 =>
        annot <- IntSize_of_nat size;
        Some (CoIR (DirH annot) (n::nil) (Some (1::nil))::nil)
    | Uint Vslice (Mint size) 1 =>
        annot <- IntSize_of_nat size;
        Some (CoIR (DirV annot) (n::nil) (Some (1::nil))::nil)
    | _ => None (* TODO *)
    end.

Function linearize_list_value {A : Type} (inL : list (@cst_or_int A)) (outL : list (@cst_or_int A)) : list (@cst_or_int A) :=
    match inL with
    | nil => outL
    | hd :: tl =>
        let outL := linearize_list_value tl outL in
        match hd with
        | CoIR d l a => match outL with
            | (CoIR d' l' a') :: tl =>
                if dir_beq d d'
                then (CoIR d (l ++ l') None) :: tl
                else hd :: outL
            | _ => hd :: outL
            end
        | CoIL n => (CoIL n) :: outL
        end
    end.

Fixpoint extract_ctxt (var_names : p) (ctxt : context) : option (list (@cst_or_int nat)) :=
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

Function eval_expr (arch : architecture) (prog : prog_ctxt) (ctxt : context) (e : expr) : option (list (@cst_or_int nat)) :=
    match e with
        | Const n None => Some (CoIL n::nil)
        | Const n (Some typ) => build_integer typ n
        | ExpVar var => eval_var ctxt var AAll
        | Tuple el => eval_expr_list arch prog ctxt el
        | Not e =>
            v <- eval_expr arch prog ctxt e;
            eval_monop (ARCH_NOT arch) v
        | Log op e1 e2 =>
            v1 <- eval_expr arch prog ctxt e1;
            v2 <- eval_expr arch prog ctxt e2;
            f <- match op with
                | And | Masked And => Some (ARCH_AND arch)
                | Or | Masked Or => Some (ARCH_OR arch)
                | Xor | Masked Xor => Some (ARCH_XOR arch)
                | Andn | Masked Andn => Some (ARCH_ANDN arch)
                | Masked (Masked _) => None
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
            eval_shift op arch v1 v2
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
with eval_expr_list (arch : architecture) (prog : prog_ctxt) (ctxt : context) (el : expr_list) : option (list (@cst_or_int nat)) :=
    match el with
    | Enil => Some nil
    | ECons e tl =>
        v <- eval_expr arch prog ctxt e;
        tl <- eval_expr_list arch prog ctxt tl;
        Some (linearize_list_value v tl)
    end.

Inductive int_or_list (A : Type) : Type :=
    | IoLL : nat -> int_or_list A
    | IoLR : list A -> int_or_list A.

Fixpoint try_take_n {A : Type} (nb : nat) (l : list A) : option ((list A) * int_or_list A) :=
    match nb with
    | 0 => Some (nil, IoLR A l)
    | S nb' => match l with
        | nil => Some (nil, IoLL A nb)
        | hd :: tl =>
            (s, e) <- try_take_n nb' tl;
            Some (hd :: s, e)
        end
    end.

Fixpoint build_ctxt_aux_take_n (nb : nat) (input : list (@cst_or_int nat)) (d : dir) : option (list nat * list (@cst_or_int nat)) :=
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
                (hd, tl) <- try_take_n nb iL;
                match tl with
                | IoLR nil => Some (hd, in_tl)
                | IoLR tl => Some(hd, CoIR d' tl None::in_tl)
                | IoLL nb =>
                    (out, rest) <- build_ctxt_aux_take_n nb in_tl d;
                    Some (hd ++ out, rest)
                end
            else None
        end
    end.

Fixpoint prod_list (l : list nat) : nat := 
    match l with
    | nil => 1
    | hd::tl => hd * prod_list tl
    end.

Fixpoint build_ctxt_aux (typ : typ) (input : list (@cst_or_int nat)) (l : list nat) : option (@cst_or_int (option nat) * list (@cst_or_int nat)) :=
    match typ with
    | Nat => match input with
        | CoIL n :: input' => Some (CoIL n, input') 
        | _ => None
        end
    | Uint d (Mint n) nb =>
        annot <- IntSize_of_nat n;
        d <- match d with
            | Hslice => Some (DirH annot)
            | Vslice => Some (DirV annot)
            | _ => None
        end;
        (valL, input') <- build_ctxt_aux_take_n (nb * prod_list l) input d;
        Some (CoIR d (map Some valL) (Some (l ++ nb::nil)), input')
    | Uint _ Mnat nb => None
    | Uint _ (Mvar _) nb => None
    | Array typ len =>
        len <- eval_arith_expr nil len;
        build_ctxt_aux typ input (len::l)
    end.

Fixpoint build_ctxt (args : p) (input : list (@cst_or_int nat)) : option context :=
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

Fixpoint convert_type (typ : typ) (l : list nat) : option (dir * list nat) :=
    match typ with
    | Nat => None
    | Uint d (Mint n) nb =>
        annot <- IntSize_of_nat n;
        d <- match d with
            | Hslice => Some (DirH annot)
            | Vslice => Some (DirV annot)
            | _ => None
        end;
        Some (d, l ++ nb::nil)
    | Uint _ Mnat nb => None
    | Uint _ (Mvar _) nb => None
    | Array typ' len =>
        len' <- eval_arith_expr nil len;
        convert_type typ' (len'::l)
    end.

Fixpoint undefined {A : Type} (n : nat) : list (option A) :=
    match n with
    | 0 => nil
    | S n' => None::undefined n'
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
Fixpoint update (form : list nat) (val : list (option nat)) (acc : access) (e : list (@cst_or_int nat)) (dir : dir) (b : bool) : option (list (option nat) * list (@cst_or_int nat)) :=
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

Fixpoint bind_aux (ctxt : context) (type_ctxt : type_ctxt) (v : var) (acc : access) (e : list (@cst_or_int nat)) (b : bool) : option (context * list (@cst_or_int nat)) :=
    match v with
    | Var v =>
        typ <- find_val type_ctxt v;
        (dir, form) <- convert_type typ nil;
        let val_init := match find_val ctxt v with
        | None => undefined (prod_list form)
        | Some (CoIL i) => Some i::nil
        | Some (CoIR _ iL _) => iL
        end in
        (val, e') <- update form val_init acc e dir b;
        Some ((v, CoIR dir val (Some form))::ctxt, e')
    | Index v ae =>
        i <- eval_arith_expr ctxt ae;
        bind_aux ctxt type_ctxt v (ASlice [:: i] acc) e b
    | Range v ae1 ae2 =>
        i1 <- eval_arith_expr ctxt ae1;
        i2 <- eval_arith_expr ctxt ae2;
        bind_aux ctxt type_ctxt v (ASlice (gen_range i1 i2) acc) e b
    | Slice v ael =>
        il <- fold_right (fun ae l =>
        l' <- l; i <- eval_arith_expr ctxt ae; Some (i::l')) (Some nil) ael;
        bind_aux ctxt type_ctxt v (ASlice il acc) e b
    end.

Fixpoint bind_aux_list ctxt type_ctxt (vl : list var) (el : list (@cst_or_int nat)) (b : bool) : option (context * list (@cst_or_int nat)) :=
    match vl with
    | nil => match el with
        | nil => Some (ctxt, el)
        | _ => None
        end
    | v :: vl' =>
        (ctxt', el') <- bind_aux ctxt type_ctxt v AAll el b;
        bind_aux_list ctxt' type_ctxt vl' el' b
    end.

Definition bind ctxt type_ctxt (vl : list var) (el : list (@cst_or_int nat)) (b : bool) : option context :=
    match bind_aux_list ctxt type_ctxt vl el b with
    | Some (ctxt', nil) => Some ctxt'
    | _ => None
    end. 

Function eval_deq (arch : architecture) (prog : prog_ctxt) (type_ctxt : type_ctxt) (ctxt : context) (d : deq) : option context :=
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

Fixpoint eval_node_inner (arch : architecture) (prog : prog_ctxt) (in_names out_names : p) (def : def_i) (i : option nat) (input : list (@cst_or_int nat)) : option (list (@cst_or_int nat)) :=
    match def, i with
    | Single temp_vars eqns, None =>
        ctxt <- build_ctxt in_names input;
        ctxt' <- eval_deq_list arch prog (build_type_ctxt (temp_vars ++ in_names ++ out_names)) ctxt eqns;
        extract_ctxt out_names ctxt'
    | Table l, None => match input with
        | (CoIL i)::nil | CoIR _ (i::nil) _::nil =>
            i' <- nth_error l i;
            Some (CoIL i'::nil)
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

Fixpoint typ_freevars (typ : typ) : Ensemble ident :=
    match typ with
    | Array typ' ae => Union ident (typ_freevars typ') (aexpr_freevars ae)
    | _ => Empty_set ident
    end.
    
Fixpoint var_freevars (v : var) : Ensemble ident :=
    match v with
    | Var var => Singleton ident var
    | Index v i => Union ident (var_freevars v) (aexpr_freevars i)
    | Range v s e => Union ident (var_freevars v) (Union ident (aexpr_freevars s) (aexpr_freevars e))
    | Slice v el => Union ident (var_freevars v) (aexprl_freevars el)
    end.

Fixpoint varl_freevars vl :=
    match vl with
    | nil => Empty_set ident
    | v :: tl => Union ident (var_freevars v) (varl_freevars tl)
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

Function deq_boundvars (d : deq) : Ensemble ident :=
    match d with 
    | Eqn v e _ => (varl_freevars v)
    | Loop i _ _ eqns _ => Union ident (Singleton ident i) (deqs_boundvars eqns)
    end
with deqs_boundvars (d : list_deq) : Ensemble ident :=
    match d with
    | Dnil => Empty_set ident
    | Dcons hd tl => Union ident (deq_boundvars hd) (deqs_boundvars tl)
    end.
