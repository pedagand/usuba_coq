Require Import String.
Require Import List.
Require Import ZArith.
Require Import Bool.
From Usuba Require Import ident.
From mathcomp Require Import seq ssrnat.

Notation " p <- e ; f " :=
    match (e : option _) return option _ with
        | Some p => f
        | None => None
    end (at level 79, p as pattern, right associativity).

(* OPERATORS *)

Inductive log_op :=
    | And
    | Or
    | Xor
    | Andn
    | Masked : log_op -> log_op.
Scheme Equality for log_op.
Definition log_op_size (x : log_op) : nat := 1.

Inductive arith_op :=
    Add | Mul | Sub | Div | Mod.
Scheme Equality for arith_op.
Definition arith_op_size (x : arith_op) : nat := 1.

Inductive shift_op :=
    Lshift | Rshift | RAshift | Lrotate | Rrotate.
Scheme Equality for shift_op.
Definition shift_op_size (x : shift_op) : nat := 1.



(** ARITHMETIC EXPRESSIONS **)

Inductive arith_expr : Type :=
    | Const_e : Z -> arith_expr
    | Var_e : ident -> arith_expr
    | Op_e : arith_op -> arith_expr -> arith_expr -> arith_expr.
Scheme Equality for arith_expr.

Fixpoint arith_expr_size (e : arith_expr) :=
    match e with
    | Const_e _ => 1
    | Var_e _ => 1
    | Op_e op e1 e2 => 1 + arith_op_size op + arith_expr_size e1 + arith_expr_size e2
    end.

Fixpoint arith_expr_list_size (el : seq arith_expr) :=
    match el with
    | nil => 0
    | h :: t => 1 + arith_expr_size h + arith_expr_list_size t
    end.

(** TYPES *)

Inductive dir :=
    | Hslice
    | Vslice
    | Bslice
    | Natdir
    | Varslice : ident -> dir
    | Mslice : nat -> dir.
Scheme Equality for dir.
Definition dir_size (d : dir) := 1.

Inductive mtyp :=
    | Mint : nat -> mtyp
    | Mnat : mtyp
    | Mvar : ident -> mtyp.
Scheme Equality for mtyp.
Definition mtyp_size (m : mtyp) := 1. 

Inductive typ :=
    | Nat : typ
    | Uint : dir -> mtyp -> typ
    | Array : typ -> nat -> typ.
(* Scheme Equality for typ. *)
Fixpoint typ_size (t : typ) :=
    match t with
    | Nat => 1
    | Uint d m => 1 + dir_size d + mtyp_size m
    | Array t e => 1 + typ_size t
    end.

(** VARIABLES *)

Inductive indexing :=
    | IInd : arith_expr -> indexing
    | IRange : arith_expr -> arith_expr -> indexing
    | ISlice : seq arith_expr -> indexing.

Inductive var :=
    | Var : ident -> var
    | Index : var -> seq indexing -> var.

Definition bvar : Type := ident * seq indexing.

Fixpoint var_size (v : var) :=
    match v with
    | Var _ => 1
    | Index v e => 1 + var_size v
    end.

Fixpoint list_var_size (v : seq var) :=
    match v with
    | nil => 0
    | hd::tl => 1 + var_size hd + list_var_size tl
    end.

Fixpoint list_eq {A} (eq : A -> A -> bool) (l1 : seq A) (l2 : seq A) :=
    match (l1, l2) with
    | (nil, nil) => true
    | (nil, _) | (_, nil) => false
    | (h1 :: t1, h2 :: t2) => eq h1 h2 && list_eq eq t1 t2
    end.

(** EXPRESSIONS *)

Inductive expr :=
  | Const : Z -> option typ -> expr
  | ExpVar : var -> expr
  | Tuple : expr_list -> expr
  | BuildArray : expr_list -> expr
  | Not : expr -> expr
  | Log : log_op -> expr -> expr -> expr
  | Arith : arith_op -> expr -> expr -> expr
  | Shift : shift_op -> expr -> arith_expr -> expr
  | Shuffle : var -> seq nat -> expr
  | Bitmask : expr -> arith_expr -> expr
  | Pack : expr -> expr -> option typ -> expr
  | Fun : ident -> expr_list -> expr
  | Fun_v : ident -> arith_expr -> expr_list -> expr
with expr_list :=
  | Enil
  | ECons : expr -> expr_list -> expr_list.

Scheme expr_find := Induction for expr Sort Prop
with expr_list_find := Induction for expr_list Sort Prop.
  
Fixpoint expr_size (e : expr) : nat :=
    match e with
    | Const n None => 1
    | Const n (Some t) => 1 + typ_size t
    | ExpVar v => 1 + var_size v
    | Tuple el => 1 + expr_list_size el
    | BuildArray el => 1 + expr_list_size el
    | Not e => 1 + expr_size e
    | Log op e1 e2 => 1 + log_op_size op + expr_size e1 + expr_size e2
    | Arith op e1 e2 => 1 + expr_size e1 + expr_size e2
    | Shift op e1 ae2 => 1 + shift_op_size op + expr_size e1 + arith_expr_size ae2
    | Shuffle v l => 1 + var_size v + List.length l
    | Bitmask e ae => 1 + expr_size e + arith_expr_size ae
    | Pack e1 e2 None => 1 + expr_size e1 + expr_size e2
    | Pack e1 e2 (Some t) => 1 + expr_size e1 + expr_size e2 + typ_size t
    | Fun id el => 1 + expr_list_size el
    | Fun_v id e el => 1 + arith_expr_size e + expr_list_size el
    end
with expr_list_size (el : expr_list) : nat :=
    match el with
    | Enil => 0
    | ECons h t => 1 + expr_size h + expr_list_size t
    end.

Inductive stmt_opt :=
    Unroll | No_unrool | Pipelined | Safe_exit.

Inductive deq :=
    | Eqn : seq bvar -> expr -> bool -> deq
    | Loop : ident -> arith_expr -> arith_expr -> list_deq -> seq stmt_opt -> deq
with list_deq :=
    | Dnil
    | Dcons : deq -> list_deq -> list_deq.

Scheme deq_find := Induction for deq Sort Prop
with list_deq_find := Induction for list_deq Sort Prop.

Fixpoint list_bvar_size (bvL : seq bvar) : nat :=
    match bvL with
    | nil => 0
    | (v, ind) :: tl => 1 + length ind + list_bvar_size tl
    end.

Fixpoint deq_size deq : nat :=
    match deq with
    | Eqn v e b => 1 + list_bvar_size v + expr_size e
    | Loop id ae1 ae2 dl stmt => 1 + arith_expr_size ae1 + arith_expr_size ae2 +
        deq_list_size dl + length stmt
    end
with deq_list_size dl := match dl with
    | Dnil => 0
    | Dcons d dl => 1 + deq_size d + deq_list_size dl
    end.

Inductive var_d_opt := Pconst | PlazyLift.

Record var_d := {
    VD_ID : ident;
    VD_TYP : typ;
    VD_OPTS : seq var_d_opt;
}.

Definition p := seq var_d.

Inductive def_i :=
    | Single : p -> list_deq -> def_i
    | Perm : seq nat -> def_i
    | Table : seq Z -> def_i
    | Multiple : list_def_i -> def_i
with list_def_i :=
    | LDnil
    | LDcons : def_i -> list_def_i -> list_def_i.

Inductive def_opt :=
    Inline | No_inline
    | Interleave : nat -> def_opt
    | No_opt | Is_table.

Record def := {
    ID : ident;
    P_IN : p;
    P_OUT : p;
    OPT : def_opt;
    NODE : def_i;
}.

Inductive def_or_inc :=
    | Def : def -> def_or_inc
    | Inc : string -> def_or_inc.

Definition prog := seq def.
