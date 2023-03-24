Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
From mathcomp Require Import all_ssreflect.
Module Import NatMap := FMapList.Make(String_as_OT).
From Coq Require Import Program Arith.
From Coq Require Recdef.

Definition ident := string.

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

Inductive arith_expr :=
    | Const_e : nat -> arith_expr
    | Var_e : ident -> arith_expr
    | Op_e : arith_op -> arith_expr -> arith_expr -> arith_expr.
Scheme Equality for arith_expr.
Function arith_expr_size (e : arith_expr) :=
    match e with
    | Const_e _ => 1
    | Var_e _ => 1
    | Op_e op e1 e2 => 1 + arith_op_size op + arith_expr_size e1 + arith_expr_size e2
    end.
Function arith_expr_list_size (el : list arith_expr) :=
    match el with
    | nil => 0
    | h :: t => 1 + arith_expr_size h + arith_expr_list_size t
    end.

Definition alpha_equal_ident (ctxt :  NatMap.t ident) (id1 : ident) (id2 : ident) : bool :=
    internal_string_beq id1 id2.


Fixpoint alpha_equal_arith_expr (ctxt :  NatMap.t ident) (ae1 : arith_expr) (ae2 : arith_expr) : bool :=
    match (ae1, ae2) with
        | (Const_e i1, Const_e i2) => i1 =? i2
        | (Var_e id1, Var_e id2) => alpha_equal_ident ctxt id1 id2
        | (Op_e op1 ae11 ae12, Op_e op2 ae21 ae22) =>
            arith_op_beq op1 op2
            && alpha_equal_arith_expr ctxt ae11 ae21
            && alpha_equal_arith_expr ctxt ae12 ae22
        | _ => false
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
Function dir_size (d : dir) := 1.

Inductive mtyp :=
    | Mint : nat -> mtyp
    | Mnat : mtyp
    | Mvar : ident -> mtyp.
Scheme Equality for mtyp.
Function mtyp_size (m : mtyp) := 1. 

Inductive typ :=
    | Nat : typ
    | Uint : dir -> mtyp -> nat -> typ
    | Array : typ -> arith_expr -> typ.
Scheme Equality for typ.
Function typ_size (t : typ) :=
    match t with
    | Nat => 1
    | Uint d m _ => 1 + dir_size d + mtyp_size m
    | Array t e => 1 + typ_size t + arith_expr_size e
    end.

(** VARIABLES *)

Inductive var :=
    | Var : ident -> var
    | Index : var -> arith_expr -> var
    | Range : var -> arith_expr -> arith_expr -> var
    | Slice : var -> list arith_expr -> var.

Function var_size (v : var) :=
    match v with
    | Var _ => 1
    | Index v e => 1 + var_size v + arith_expr_size e
    | Range v e1 e2 => 1 + var_size v + arith_expr_size e1 + arith_expr_size e2
    | Slice v el => 1 + var_size v + arith_expr_list_size el
    end.

Function list_var_size (v : list var) :=
    match v with
    | nil => 0
    | hd::tl => 1 + var_size hd + list_var_size tl
    end.

Fixpoint list_eq {A} (eq : A -> A -> bool) (l1 : list A) (l2 : list A) :=
    match (l1, l2) with
    | (nil, nil) => true
    | (nil, _) | (_, nil) => false
    | (h1 :: t1, h2 :: t2) => eq h1 h2 && list_eq eq t1 t2
    end.

Fixpoint alpha_equal_var (ctxt :  NatMap.t ident) (v1 : var) (v2 : var) :=
    match (v1, v2) with
    | (Var id1, Var id2) => alpha_equal_ident ctxt id1 id2
    | (Index v1 ae1, Index v2 ae2) =>
        alpha_equal_var ctxt v1 v2
        && alpha_equal_arith_expr ctxt ae1 ae2
    | (Range v1 ae11 ae12, Range v2 ae21 ae22) =>
        alpha_equal_var ctxt v1 v2
        && alpha_equal_arith_expr ctxt ae11 ae21
        && alpha_equal_arith_expr ctxt ae12 ae22
    | (Slice v1 ael1, Slice v2 ael2) =>
        alpha_equal_var ctxt v1 v2
        && list_eq (alpha_equal_arith_expr ctxt) ael1 ael2
    | _ => false
    end.

(** EXPRESSIONS *)

Inductive expr :=
  | Const : nat -> option typ -> expr
  | ExpVar : var -> expr
  | Tuple : expr_list -> expr
  | Not : expr -> expr
  | Log : log_op -> expr -> expr -> expr
  | Arith : arith_op -> expr -> expr -> expr
  | Shift : shift_op -> expr -> arith_expr -> expr
  | Shuffle : var -> list nat -> expr
  | Bitmask : expr -> arith_expr -> expr
  | Pack : expr -> expr -> option typ -> expr
  | Fun : ident -> expr_list -> expr
  | Fun_v : ident -> arith_expr -> expr_list -> expr
with expr_list :=
  | Enil
  | ECons : expr -> expr_list -> expr_list.

Scheme expr_find := Induction for expr Sort Prop
with expr_list_find := Induction for expr_list Sort Prop.
  
Function expr_size (e : expr) : nat :=
    match e with
    | Const n None => 1
    | Const n (Some t) => 1 + typ_size t
    | ExpVar v => 1 + var_size v
    | Tuple el => 1 + expr_list_size el
    | Not e => 1 + expr_size e
    | Log op e1 e2 => 1 + log_op_size op + expr_size e1 + expr_size e2
    | Arith op e1 e2 => 1 + expr_size e1 + expr_size e2
    | Shift op e1 e2 => 1 + shift_op_size op + expr_size e1 + arith_expr_size e2
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

Function alpha_equal_expr (ctxt :  NatMap.t ident) (e1 : expr) (e2 : expr) : bool :=
    match (e1, e2) with
    | (Const i1 t1, Const i2 t2) => (i1 =? i2) && t1 == t2
    | (ExpVar v1, ExpVar v2) => alpha_equal_var ctxt v1 v2
    | (Tuple el1, Tuple el2) => alpha_equal_expr_list ctxt el1 el2
    | (Not e1, Not e2) => alpha_equal_expr ctxt e1 e2
    | (Log op1 e11 e12, Log op2 e21 e22) =>
        log_op_beq op1 op2 && alpha_equal_expr ctxt e11 e21 && alpha_equal_expr ctxt e12 e22
    | (Arith op1 e11 e12, Arith op2 e21 e22) =>
        arith_op_beq op1 op2 && alpha_equal_expr ctxt e11 e21 && alpha_equal_expr ctxt e12 e22
    | (Shift op1 e1 ae1, Shift op2 e2 ae2) =>
        shift_op_beq op1 op2 && alpha_equal_expr ctxt e1 e2
        && alpha_equal_arith_expr ctxt ae1 ae2
    | (Shuffle v1 il1, Shuffle v2 il2) =>
        alpha_equal_var ctxt v1 v2 && list_eq Nat.eqb il1 il2
    | (Bitmask e1 ae1, Bitmask e2 ae2) =>
        alpha_equal_expr ctxt e1 e2 && alpha_equal_arith_expr ctxt ae1 ae2
    | (Pack e11 e12 t1, Pack e21 e22 t2) =>
        alpha_equal_expr ctxt e11 e21 && alpha_equal_expr ctxt e12 e22 && t1 == t2
    | (Fun id1 el1, Fun id2 el2) =>
        alpha_equal_ident ctxt id1 id2 && alpha_equal_expr_list ctxt el1 el2
    | (Fun_v id1 ae1 el1, Fun_v id2 ae2 el2) =>
        alpha_equal_ident ctxt id1 id2
        && alpha_equal_arith_expr ctxt ae1 ae2
        && alpha_equal_expr_list ctxt el1 el2
    | _ => false
    end
with alpha_equal_expr_list (ctxt :  NatMap.t ident) (el1 : expr_list) (el2 : expr_list) : bool :=
    match (el1, el2) with
        | (Enil, Enil) => true
        | (Enil, _) | (_, Enil) => false
        | (ECons e1 t1, ECons e2 t2) =>
            alpha_equal_expr ctxt e1 e2
            && alpha_equal_expr_list ctxt t1 t2
    end.

Inductive stmt_opt :=
    Unroll | No_unrool | Pipelined | Safe_exit.

Inductive deq :=
    | Eqn : list var -> expr -> bool -> deq
    | Loop : ident -> arith_expr -> arith_expr -> list_deq -> list stmt_opt -> deq
with list_deq :=
    | Dnil
    | Dcons : deq -> list_deq -> list_deq.

Scheme deq_find := Induction for deq Sort Prop
with list_deq_find := Induction for list_deq Sort Prop.

Function deq_size deq : nat :=
    match deq with
    | Eqn v e b => 1 + list_var_size v + expr_size e
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
    VD_OPTS : list var_d_opt;
}.

Definition p := list var_d.

Inductive def_i :=
    | Single : p -> list_deq -> def_i
    | Perm : list nat -> def_i
    | Table : list nat -> def_i
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

Definition prog := list def.
