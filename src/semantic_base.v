Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import all_ssreflect.

From Usuba Require Import utils ident usuba_AST arch.

Fixpoint find_val {A : Type} (ctxt : list (ident * A)) (i : ident) : option A :=
    match ctxt with
        | nil => None
        | ((name, val)::tl) =>
            if ident_beq i name
            then Some val
            else find_val tl i
    end.

Fixpoint gen_range_incr (i1 i2 : nat) : list nat :=
    if i1 <? i2
    then
    match i2 with
    | 0 => nil
    | S i2' => gen_range_incr i1 i2'
    end ++ i2::nil
    else
    [:: i2]
    .
    
Fixpoint gen_range_decr (i1 i2 : nat) : list nat :=
    if i1 <? i2
    then
    nil
    else
    i1::match i1 with
    | 0 => nil
    | S i1' => gen_range_decr i1' i2
    end.
    
Definition gen_range (i1 i2 : nat) : list nat :=
    if i1 <=? i2
    then gen_range_incr i1 i2
    else gen_range_decr i1 i2.

(* Utilities to modify context *)

Fixpoint map_ctxt {A B : Type} (f : A -> B) (ctxt : list (ident * A)) : list (ident * B) :=
    match ctxt with
    | nil => nil
    | (i, v)::tl => (i, f v)::map_ctxt f tl
    end.

Fixpoint update_ctxt {A : Type} (ctxt : list (ident * A)) (i : ident) (update : A -> option A) : option (list (ident * A)) :=
    match ctxt with
    | nil => None
    | (id, val)::tl =>
        if ident_beq i id
        then
            val' <- update val;
            Some ((id, val')::tl)
        else
            tl' <- update_ctxt tl i update;
            Some ((id, val)::tl')
    end.

Fixpoint list_of_expr_list (el : expr_list) : list expr :=
    match el with
    | Enil => nil
    | ECons hd tl => hd :: list_of_expr_list tl
    end.

(* List utils *)

Fixpoint zip {A B} (l1 : seq A) (l2 : seq B) :=
    match l1 with
    | nil => nil
    | h1::t1 =>
        match l2 with
        | nil => nil
        | h2::t2 => (h1, h2) :: zip t1 t2
        end
    end.

Fixpoint list_map2 {A B C : Type} (op : A -> B -> C) (l1 : list A) (l2 : list B) : option (list C) :=
    match l1, l2 with
    | nil, nil => Some nil
    | h1::t1, h2::t2 =>
        tl <- list_map2 op t1 t2;
        Some (op h1 h2::tl)
    | _, _ => None
    end.

Fixpoint prod_list (l : list nat) : nat := 
    match l with
    | nil => 1
    | hd::tl => hd * prod_list tl
    end.

Fixpoint scm (l1 l2 : list nat) : list nat :=
    match l1 with
    | nil => nil
    | h1::t1 => match l2 with
        | nil => nil
        | h2::t2 =>
            if Nat.eqb h1 h2
            then h1::scm t1 t2
            else (prod_list l1)::nil
        end
    end.

(* Definition of Values *)

Inductive cst_or_int {A : Type} :=
    | CoIL : Z -> cst_or_int
    | CoIR : dir -> list A -> list nat -> cst_or_int.
Scheme Equality for option.
Scheme Equality for list.

Definition Value := list (@cst_or_int Z).

Definition context : Type := list (ident * @cst_or_int (option Z)).

Fixpoint get_dir (l : list (@cst_or_int Z)) : option dir :=
    match l with
    | nil => None
    | CoIL _ ::tl => get_dir tl
    | CoIR d _ _::_ => Some d
    end.

Fixpoint coerce_to (d : dir) (l1 : list (@cst_or_int Z)) : option (list Z) :=
    match l1 with
    | nil => Some nil
    | CoIL n::tl =>
        tl <- coerce_to d tl; Some (n::tl)
    | CoIR d' iL _::tl =>
        if dir_beq d d'
        then
            tl <- coerce_to d tl;
            Some (iL ++ tl)
        else None
    end.
    
Fixpoint sum_length {A} (l: list (@cst_or_int A)) : nat :=
    match l with
    | nil => 0
    | CoIL _::tl => 1 + sum_length tl
    | CoIR _ l _::tl => length l + sum_length tl
    end.

Definition compute_form {A} (l1 : list (@cst_or_int A)) : list nat :=
    match l1 with
    | CoIL _::nil => 1::nil
    | CoIR _ _ form::nil => form
    | _ => sum_length l1::nil
    end.

Definition eval_binop (binop : dir -> option (Z -> Z -> Z)) (l1 l2 : list (@cst_or_int Z)) : option (list (@cst_or_int Z)) :=
    d <- match get_dir l1 with
        | None => get_dir l2
        | Some d => Some d
        end;
    v1 <- coerce_to d l1;
    v2 <- coerce_to d l2;
    op <- binop d;
    v3 <- list_map2 op v1 v2;
    let form1 := compute_form l1 in
    let form2 := compute_form l2 in
    Some (CoIR d v3 (scm form1 form2)::nil).

Definition eval_monop_coi (monop : dir -> option (Z -> Z)) (v : @cst_or_int Z) : option (@cst_or_int Z) :=
    match v with
    | CoIL _ => None
    | CoIR d i l => 
        op <- monop d;
        Some (CoIR d (map op i) l)
    end.

Fixpoint eval_monop (monop : dir -> option (Z -> Z)) (v : list (@cst_or_int Z)) : option (list (@cst_or_int Z)) :=
    match v with
    | nil => Some nil
    | hd::tl =>
        hd' <- eval_monop_coi monop hd;
        tl' <- eval_monop monop tl;
        Some (hd' :: tl')
    end.

Definition eval_shift (arch : architecture) (op : shift_op) (v : list (@cst_or_int Z)) (v2 : nat) : option (list (@cst_or_int Z)) :=
    match v with
    | CoIR d (i::nil) len::nil =>
        i' <- shift_wrapper (IMPL_SHIFT arch) op v2 d i;
        Some (CoIR d (i'::nil) len::nil)
    | CoIR d i len::nil => match op with
        | Lshift =>
            (hd, tl) <- take_n v2 i;
            Some (CoIR d (app tl (map (fun _=> 0%Z) hd)) len::nil)
        | _ => None
        end
    | _ => None
    end.

Fixpoint find_const (ctxt : context) (var : ident) : option nat :=
    match ctxt with
        | nil => None
        | ((name, v)::tl) =>
            if ident_beq var name
            then match v with
                | CoIL i => if (0 <=? i)%Z then Some (Z.to_nat i) else None
                | _ => None
                end
            else find_const tl var
    end.

Fixpoint find_node (p : prog) (i : ident) : option def :=
    match p with
        | nil => None
        | node::tl =>
            if ident_beq i (ID node)
            then Some node
            else find_node tl i
    end.
    
Fixpoint eval_arith_expr_inner (ctxt : context) (e : arith_expr) : option Z :=
    match e with
        | Const_e i => Some i
        | Var_e var => 
            i <- find_const ctxt var; Some (Z.of_nat i)
        | Op_e op e1 e2 =>
            v1 <- eval_arith_expr_inner ctxt e1;
            v2 <- eval_arith_expr_inner ctxt e2;
            match op with
                | Add => Some (v1 + v2)%Z
                | Mul => Some (v1 * v2)%Z
                | Sub => Some (v1 - v2)%Z
                | Mod => Some (v1 mod v2)%Z
                | Div => Some (v1 / v2)%Z
            end
    end.

Definition eval_arith_expr (ctxt : context) (e : arith_expr) : option nat :=
    i <- eval_arith_expr_inner ctxt e;
    if (i <? 0)%Z
    then None
    else Some (Z.to_nat i).

Fixpoint remove_option_from_list {A : Type} (l : list (option A)) : option (list A) :=
    match l with
    | nil => Some nil
    | hd::tl =>
        hd' <- hd;
        tl' <- remove_option_from_list tl;
        Some (hd'::tl')
    end.

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
    
Definition type_ctxt : Type := list (ident * typ).
Definition node_sem_type := option nat -> list (@cst_or_int Z) -> option (list (@cst_or_int Z)).
Definition prog_ctxt := list (ident * node_sem_type).

Fixpoint get_node (prog : prog_ctxt) (id : ident) : option node_sem_type :=
    match prog with
    | nil => None
    | (name, f) :: tl => if ident_beq name id
        then Some f
        else get_node tl id
    end.

Definition build_integer (typ : typ) (n : Z) : option (list (@cst_or_int Z)) :=
    match typ with
    | Nat => Some (CoIL n::nil)
    | Uint Hslice (Mint size) =>
        annot <- IntSize_of_nat size;
        Some (CoIR (DirH annot) (n::nil) nil::nil)
    | Uint Vslice (Mint size) =>
        annot <- IntSize_of_nat size;
        Some (CoIR (DirV annot) (n::nil) nil::nil)
    | Uint Bslice (Mint 1) =>
        if (1 <? n)%Z
        then None
        else
            Some (CoIR DirB (n::nil) nil::nil)
    | _ => None (* TODO *)
    end.

Inductive Sum (A : Type) (B : Type) : Type :=
    | SumL : A -> Sum A B
    | SumR : B -> Sum A B.

Arguments SumL {_} {_} _.
Arguments SumR {_} {_} _.


Fixpoint merge_inner fuel form1 form2 : Sum (nat * nat * list nat) (list nat) :=
    match fuel with
    | 0 => SumL (prod_list form1, prod_list form2, nil)
    | S fuel => if length form1 <? length form2
        then match form2 with
            | nil => SumL (0, 0, nil)
            | h2::t2 => match merge_inner fuel form1 t2 with
                    | SumL (len1, len2, form) => SumL (len1, h2 * len2, form)
                    | SumR l => SumR (h2 + 1::l)
                end
            end
        else if length form2 <? length form1
        then match form1 with
            | nil => SumL (0, 0, nil)
            | h1::t1 => match merge_inner fuel t1 form2 with
                    | SumL (len1, len2, form) => SumL (h1 * len1, len2, form)
                    | SumR l => SumR (h1 + 1::l)
                end
            end
        else match form1 with
            | nil => match form2 with
                | nil => SumR nil
                | _ => SumL (0, 0, nil)
                end
            | h1::t1 => match form2 with
                | nil => SumL (0, 0, nil)
                | h2::t2 => match merge_inner fuel t1 t2 with
                    | SumL (len1, len2, form) => SumL (h1 * len1, h2 * len2, form)
                    | SumR l =>
                        if Nat.eqb h1 h2
                        then SumR (h1::l)
                        else SumL (h1, h2, l)
                    end
                end
            end
    end.

Definition merge form1 form2 :=
    match merge_inner (length form1 + length form2) form1 form2 with
    | SumR form => 2::form
    | SumL (len1, len2, form) => (len1 + len2::form)
    end.


Fixpoint linearize_list_value {A : Type} (inL : list (@cst_or_int A)) (outL : list (@cst_or_int A)) : list (@cst_or_int A) :=
    match inL with
    | nil => outL
    | hd :: tl =>
        let outL := linearize_list_value tl outL in
        match hd with
        | CoIR d l form => match outL with
            | (CoIR d' l' form') :: tl =>
                if dir_beq d d'
                then (CoIR d (l ++ l') (merge form form')) :: tl
                else hd :: outL
            | _ => hd :: outL
            end
        | CoIL n => (CoIL n) :: outL
        end
    end.

Inductive access : Type :=
    | AAll : access
    | AInd : nat -> access -> access
    | ASlice : list nat -> access -> access.

Fixpoint access_of_ind (ctxt : context) (l : list indexing) : option access :=
    match l with
    | nil => Some AAll
    | IInd ae::tl =>
        i <- eval_arith_expr ctxt ae;
        acc <- access_of_ind ctxt tl;
        Some (AInd i acc)
    | ISlice il::tl =>
        il' <- fold_right (fun ae tl =>
            tl' <- tl;
            i <- eval_arith_expr ctxt ae;
            Some (i::tl')) (Some nil) il;
        acc <- access_of_ind ctxt tl;
        Some (ASlice il' acc)
    | IRange ae1 ae2::tl =>
        i1 <- eval_arith_expr ctxt ae1;
        i2 <- eval_arith_expr ctxt ae2;
        acc <- access_of_ind ctxt tl;
        Some (ASlice (gen_range i1 i2) acc)
    end.

Fixpoint try_take_n {A : Type} (nb : nat) (l : list A) : ((list A) * Sum nat (list A)) :=
    match nb with
    | 0 => (nil, SumR l)
    | S nb' => match l with
        | nil => (nil, SumL nb)
        | hd :: tl =>
            let (s, e) := try_take_n nb' tl in
            (hd :: s, e)
        end
    end.

Fixpoint undefined {A : Type} (n : nat) : list (option A) :=
    match n with
    | 0 => nil
    | S n' => None::undefined n'
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

Definition proj_types (p : var_d) : ident * typ := (VD_ID p, VD_TYP p).

(* Transposition of list of intergers in binary representations *)

Fixpoint transpose_nat_list (n : nat) (l : list Z) : list Z :=
    match n with
    | 0 => nil
    | S n' =>
        let (num, l') :=
            fold_left (fun (p : Z * list Z) i =>
                let (nb, tl) := p in (2 * nb + (i mod 2), tl ++ [:: i / 2])%Z)
                l (0%Z, nil)
        in transpose_nat_list n' l' ++ [:: num]
    end.

Fixpoint transpose_nat_list2 (iL : list Z) (len : nat) : list Z :=
    match iL with
    | nil => map (fun _=> 0%Z) (@undefined Z len)
    | hd::tl =>
        let iL' := transpose_nat_list2 tl len in
        let t2 := transpose_nat_list len (hd::nil) in
        match list_map2 (fun i j => i * 2 + j)%Z iL' t2 with
        | Some l => l
        | None => nil
        end
    end.


(* Monomorphisation of functions *)

(* TODO handle multiple type parameters *)
Record monomorph_info : Type := {
    DIR_MONO : option usuba_AST.dir;
    SIZE_MONO : option nat;
}.

Fixpoint convert_type (typ : typ) : option (dir * list nat) :=
    match typ with
    | Nat => None
    | Uint d (Mint n) =>
        annot <- IntSize_of_nat n;
        d <- match d with
            | Hslice => Some (DirH annot)
            | Vslice => Some (DirV annot)
            | Bslice => Some DirB
            | Varslice _ => Some (Dir_S annot) 
            | _ => None
        end;
        Some (d, nil)
    | Uint _ Mnat => None
    | Uint d (Mvar _) =>
        d <- match d with
            | Hslice => Some DirH_
            | Vslice => Some DirV_
            | Varslice _ => Some DirUnknow 
            | _ => None
        end;
        Some (d, nil)
    | Array typ' len =>
        (d, l) <- convert_type typ';
        Some (d, len::l)
    end.

Fixpoint extract_n {A : Type} (n : nat) (l : list (@cst_or_int A)) : option (list cst_or_int) :=
    match l with
    | nil => match n with
        | 0 => Some nil
        | _ => None
        end
    | CoIL _::tl => match n with
        | 0 => Some l
        | S n' => extract_n n' tl
        end
    | CoIR d iL form::tl =>
        match try_take_n n iL with
        | (_, SumR nil) => Some tl
        | (_, SumR iL') => Some (CoIR d iL' (n::nil)::tl)
        | (_, SumL n') => extract_n n' tl
        end
    end.

Fixpoint extract_dir {A : Type} (n : nat) (l : list (@cst_or_int A)) : option usuba_AST.dir :=
    match l with
    | nil => None
    | CoIL _::tl => match n with
        | 0 => None
        | S n' => extract_dir n' tl
        end
    | CoIR d iL form::tl =>
        match n with
        | 0 => None
        | _ => 
            match d with
            | DirB   => Some Bslice
            | DirH _ => Some Hslice
            | DirV _ => Some Vslice
            | _ => None
            end
        end
    end.

Fixpoint extract_size {A : Type} (n : nat) (l : list (@cst_or_int A)) : option nat :=
    match l with
    | nil => None
    | CoIL _::tl => match n with
        | 0 => None
        | S n' => extract_size n' tl
        end
    | CoIR d iL form::tl =>
        match n with
        | 0 => None
        | _ => 
            match d with
            | DirB   => Some 1
            | DirH i | DirV i => Some i
            | _ => None
            end
        end
    end.

Fixpoint infer_types (args : p) (input : list (@cst_or_int Z)) : option monomorph_info :=
    match args with
    | nil => Some {| DIR_MONO := None; SIZE_MONO := None |}
    | hd :: tl => 
        (d, form) <- convert_type (VD_TYP hd);
        let ed := extract_dir (prod_list form) input in
        let es := extract_size (prod_list form) input in
        input' <- extract_n (prod_list form) input;
        info <- infer_types tl input';
        match d with
        | DirUnknow =>
            let d := match (ed, DIR_MONO info) with
                | (Some d, _) | (_, Some d) => Some d
                | (None, None) => None
            end in
            let s := match (es, SIZE_MONO info) with
                | (Some s, _) | (_, Some s) => Some s
                | (None, None) => None
            end in
            Some {| DIR_MONO := d; SIZE_MONO := s; |}
        | Dir_S i =>
            let d := match (ed, DIR_MONO info) with
                | (Some d, _) | (_, Some d) => Some d
                | (None, None) => None
            end in
            Some {| DIR_MONO := d; SIZE_MONO := SIZE_MONO info; |}
        | DirH_ | DirV_ =>
            let s := match (es, SIZE_MONO info) with
                | (Some s, _) | (_, Some s) => Some s
                | (None, None) => None
            end in
            Some {| DIR_MONO := DIR_MONO info; SIZE_MONO := s; |}
        | _ => Some info
        end
    end.

Fixpoint subst_infer_typ (infered : monomorph_info) (type : typ) : typ :=
    match type with
    | Uint d m =>
        let d' := match (d, DIR_MONO infered) with
            | (Varslice _, Some d) => d
            | _ => d
        end in
        let m' := match (m, SIZE_MONO infered) with
            | (Mvar _, Some i) => Mint i
            | _ => m
        end in Uint d' m'
    | Nat => Nat
    | Array t len => Array (subst_infer_typ infered t) len
    end.

Fixpoint subst_infer_p (infered : monomorph_info) (args : p) : p :=
    match args with
    | nil => nil
    | hd :: tl =>
        let tl := subst_infer_p infered tl in
        {|
            VD_ID := VD_ID hd;
            VD_TYP := subst_infer_typ infered (VD_TYP hd);
            VD_OPTS := VD_OPTS hd;
        |}::tl
    end.

Fixpoint subst_infer_expr (infered : monomorph_info) (e : expr) : expr :=
    match e with
    | Const _ None | ExpVar _ | Shuffle _ _ => e
    | Const i (Some t) => Const i (Some (subst_infer_typ infered t))
    | Tuple el => Tuple (subst_infer_list_expr infered el)
    | BuildArray el => BuildArray (subst_infer_list_expr infered el)
    | Not e => Not (subst_infer_expr infered e)
    | Log op e1 e2 => Log op (subst_infer_expr infered e1) (subst_infer_expr infered e2)
    | Arith op e1 e2 => Arith op (subst_infer_expr infered e1) (subst_infer_expr infered e2)
    | Shift op e ae => Shift op (subst_infer_expr infered e) ae
    | Bitmask e ae => Bitmask (subst_infer_expr infered e) ae
    | Pack e1 e2 o_typ => Pack (subst_infer_expr infered e1) (subst_infer_expr infered e2) (option_map (subst_infer_typ infered) o_typ)
    | Fun v el => Fun v (subst_infer_list_expr infered el)
    | Fun_v v ae el => Fun_v v ae (subst_infer_list_expr infered el)
    end
with subst_infer_list_expr (infered : monomorph_info) (el : expr_list) : expr_list :=
    match el with
    | Enil => Enil
    | ECons hd tl =>
        ECons (subst_infer_expr infered hd)
            (subst_infer_list_expr infered tl)
    end.

Fixpoint subst_infer_deq (infered : monomorph_info) (d : deq) : deq :=
    match d with
    | Eqn v e b => Eqn v (subst_infer_expr infered e) b
    | Loop i ae1 ae2 eqns opt =>
        Loop i ae1 ae2 (subst_infer_list_deq infered eqns) opt
    end
with subst_infer_list_deq (infered : monomorph_info) (eqns : list_deq) : list_deq :=
    match eqns with
    | Dnil => Dnil
    | Dcons hd tl =>
        Dcons (subst_infer_deq infered hd)
            (subst_infer_list_deq infered tl)
    end.

Fixpoint subst_infer_def (infered : monomorph_info) (node : def_i) : def_i :=
    match node with
    | Single tmp eqns => Single (subst_infer_p infered tmp) (subst_infer_list_deq infered eqns)
    | Perm p => Perm p
    | Table t => Table t
    | Multiple l => Multiple (subst_infer_list_def infered l)
    end
with subst_infer_list_def (infered : monomorph_info) (l : list_def_i) : list_def_i :=
    match l with
    | LDnil => LDnil
    | LDcons hd tl =>
        LDcons (subst_infer_def infered hd)
            (subst_infer_list_def infered tl)
    end.

(* Flattening of declarations *)

Fixpoint subst_aexpr (ctxt : list (ident * nat)) (ae : arith_expr) : arith_expr :=
    match ae with
    | Const_e _ => ae
    | Var_e id =>
        match find_val ctxt id with
        | None => ae
        | Some val => Const_e (Z.of_nat val)
        end
    | Op_e aop ae1 ae2 =>
        Op_e aop (subst_aexpr ctxt ae1) (subst_aexpr ctxt ae2)
    end.

Definition subst_aexprl (ctxt : list (ident * nat)) (aeL : list arith_expr) : list arith_expr :=
    [seq subst_aexpr ctxt ae | ae <- aeL ].

Definition subst_indexing (ctxt : list (ident * nat)) (ind : indexing) : indexing :=
    match ind with
    | IInd ae => IInd (subst_aexpr ctxt ae)
    | IRange ae1 ae2 => IRange (subst_aexpr ctxt ae1) (subst_aexpr ctxt ae2)
    | ISlice aeL => ISlice (subst_aexprl ctxt aeL)
    end.

Definition subst_indexingl (ctxt : list (ident * nat)) (indL : list indexing) : list indexing :=
    [seq subst_indexing ctxt ind | ind <- indL ].

Fixpoint subst_var (ctxt : list (ident * nat)) (v : var) : var :=
    match v with
    | Var _ => v
    | Index var' indL => Index (subst_var ctxt var') (subst_indexingl ctxt indL)
    end.

Definition subst_varl (ctxt : list (ident * nat)) (vL : list var) : list var :=
    [seq subst_var ctxt v | v <- vL ].


Definition subst_bvar (ctxt : list (ident * nat)) (bv : bvar) : bvar :=
    (bv.1, subst_indexingl ctxt bv.2).

Definition subst_bvarl (ctxt : list (ident * nat)) (vL : list bvar) : list bvar :=
    [seq subst_bvar ctxt bv | bv <- vL ].
        
Fixpoint subst_expr (ctxt : list (ident * nat)) (e : expr) : expr :=
    match e with
    | Const _ _ => e
    | ExpVar v => ExpVar (subst_var ctxt v)
    | Tuple el => Tuple (subst_exprl ctxt el)
    | BuildArray el => BuildArray (subst_exprl ctxt el)
    | Not e => Not (subst_expr ctxt e)
    | Log lop e1 e2 => Log lop (subst_expr ctxt e1) (subst_expr ctxt e2)
    | Arith aop e1 e2 => Arith aop (subst_expr ctxt e1) (subst_expr ctxt e2)
    | Shift sop e ae => Shift sop (subst_expr ctxt e) (subst_aexpr ctxt ae)
    | Shuffle v l => Shuffle (subst_var ctxt v) l
    | Bitmask e ae => Bitmask (subst_expr ctxt e) (subst_aexpr ctxt ae)
    | Pack e1 e2 typ => Pack (subst_expr ctxt e1) (subst_expr ctxt e2) typ
    | Fun f el => Fun f (subst_exprl ctxt el)
    | Fun_v f ae el => Fun_v f (subst_aexpr ctxt ae) (subst_exprl ctxt el)
    end
with subst_exprl ctxt el :=
    match el with
    | Enil => Enil
    | ECons hd tl => ECons (subst_expr ctxt hd) (subst_exprl ctxt tl)
    end.

Fixpoint loop_build (s_i e_i : nat) : list nat :=
    if (Nat.ltb e_i s_i)
    then nil
    else
        match e_i with
        | 0 => e_i::nil
        | S e_i' =>
            e_i::loop_build s_i e_i'
    end.
    
Fixpoint list_of_list_deq (ctxt : list (ident * nat)) (deqL : list_deq) : option (list (seq bvar * expr)) :=
    match deqL with
    | Dnil => Some nil
    | Dcons hd tl =>
        tl' <- list_of_list_deq ctxt tl;
        match hd with
        | Eqn vL e _ => Some ((subst_bvarl ctxt vL, subst_expr ctxt e)::tl')
        | Loop i start_e end_e eqns opt =>
            start_i <- eval_arith_expr nil (subst_aexpr ctxt start_e);
            end_i <- eval_arith_expr nil (subst_aexpr ctxt end_e);
            let vals := loop_build start_i end_i in
            fold_right (fun val tl =>
                tl' <- tl;
                l <- list_of_list_deq ((i, val)::ctxt) eqns;
                Some (l ++ tl')) (Some tl') vals
        end
    end.
