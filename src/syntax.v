Require Import String.
Require Import List.
Require Import ZArith.
From Usuba Require Import ident usuba_AST.

Declare Scope Usuba.
Delimit Scope Usuba with usuba.
Declare Scope Usuba_var_decl.
Delimit Scope Usuba_var_decl with ua_var_decl.
Declare Scope Usuba_type.
Delimit Scope Usuba_type with ua_type.
Declare Scope Usuba_eqn.
Delimit Scope Usuba_eqn with ua_eqn.
Declare Scope Usuba_expr.
Delimit Scope Usuba_expr with ua_expr.
Declare Scope Usuba_arith_expr.
Delimit Scope Usuba_arith_expr with ua_aexpr.
Declare Scope Usuba_var.
Delimit Scope Usuba_var with ua_var.

Coercion ExpVar : var >-> expr.
Coercion Var_e : ident >-> arith_expr.
Definition c_e n := Const_e (Z.of_nat n).
Coercion c_e : nat >-> arith_expr.
Coercion Const_e : Z >-> arith_expr.

Definition c x := Const x None.
Coercion c : Z >-> expr.
Definition c' x := Const (Z.of_nat x) None.
Coercion c' : nat >-> expr.
Coercion Var : ident >-> var.
Coercion Id_s : string >-> ident.

Notation "x '&' y" := (Log And (x)%ua_expr (y)%ua_expr) (at level 87, left associativity) : Usuba_expr.
Notation "x 'xor' y" := (Log Xor (x)%ua_expr (y)%ua_expr) (at level 87, left associativity) : Usuba_expr.
Notation "x '<<' y" := (Shift Lshift (x)%ua_expr (y)%ua_aexpr) (at level 87, left associativity) : Usuba_expr.
Notation "x '>>' y" := (Shift Rshift (x)%ua_expr (y)%ua_aexpr) (at level 87, left associativity) : Usuba_expr.
Notation "x '<<<' y" := (Shift Lrotate (x)%ua_expr (y)%ua_aexpr) (at level 87, left associativity) : Usuba_expr.
Notation "x '>>>' y" := (Shift Rrotate (x)%ua_expr (y)%ua_aexpr) (at level 87, left associativity) : Usuba_expr.
Notation "x '+' y"   := (Arith Add (x)%ua_expr (y)%ua_expr) (at level 50, left associativity) : Usuba_expr.
Notation "x '-' y"   := (Arith Sub (x)%ua_expr (y)%ua_expr) (at level 50, left associativity) : Usuba_expr.
Notation "x '*' y"   := (Arith Mul (x)%ua_expr (y)%ua_expr) (at level 40, left associativity) : Usuba_expr.
Notation "x '/' y"   := (Arith Div (x)%ua_expr (y)%ua_expr) (at level 40, left associativity) : Usuba_expr.
Notation "f '@' '[' x , .. , y ']'" := (Fun (f)%string (ECons ((x)%ua_expr : expr) .. (ECons ((y)%ua_expr : expr) Enil) ..)) (at level 75, no associativity) : Usuba_expr.
Notation "'[' x , .. , y ']'" := (Tuple (ECons ((x)%ua_expr : expr) .. (ECons ((y)%ua_expr : expr) Enil) ..)) (at level 87, no associativity) : Usuba_expr.

Notation "f '$' '[' x , .. , y ']'" := (Slice (f)%ua_var (cons ((x)%ua_aexpr : arith_expr) .. (cons ((y)%ua_aexpr : arith_expr) nil) ..)) (at level 75, no associativity) : Usuba_var.
Notation "f '$' '[' x , .. , y ']'" := (Slice (f)%ua_var (cons ((x)%ua_aexpr : arith_expr) .. (cons ((y)%ua_aexpr : arith_expr) nil) ..)) (at level 75, no associativity) : Usuba_expr.

Notation "x '+' y"   := (Op_e Add (x)%ua_aexpr (y)%ua_aexpr) (at level 50, left associativity) : Usuba_arith_expr.
Notation "x '-' y"   := (Op_e Sub (x)%ua_aexpr (y)%ua_aexpr) (at level 50, left associativity) : Usuba_arith_expr.
Notation "x '*' y"   := (Op_e Mul (x)%ua_aexpr (y)%ua_aexpr) (at level 40, left associativity) : Usuba_arith_expr.
Notation "x '/' y"   := (Op_e Div (x)%ua_aexpr (y)%ua_aexpr) (at level 40, left associativity) : Usuba_arith_expr.

Notation "v '[' e ']'" := (Index (v)%ua_var  (e)%ua_aexpr) (at level 61, left associativity) : Usuba_var.
Notation "v '[' e ']'" := (Index (v)%ua_var  (e)%ua_aexpr) (at level 61, left associativity) : Usuba_expr.
Notation "t '[' e ']'" := (Array (t)%ua_type (e)%ua_aexpr) (at level 61, left associativity) : Usuba_type.

Notation " a '<|-' b" := (Eqn (a)%ua_var (b)%ua_expr false)
    (at level 89, right associativity) : Usuba_eqn.

Notation " a '<:-' b" := (Eqn (a)%ua_var (b)%ua_expr true)
    (at level 89, right associativity) : Usuba_eqn.

(* Notation "'(' a1 , .. , a2 ')' '<-' b" := (Eqn (cons (a1)%ua_var .. (cons (a2)%ua_var nil) ..) (b)%ua_expr false)
    (at level 90, right associativity) : Usuba_eqn.

Notation "'(' a1 , .. , a2 ')' '<:-' b" := (Eqn (cons (a1)%ua_var .. (cons (a2)%ua_var nil) ..) (b)%ua_expr true)
    (at level 90, right associativity) : Usuba_eqn. *)

Notation "'for' var 'in' s 'to' e 'do' e1 ; .. ; e2 'done'" :=
    (Loop var (s)%ua_aexpr (e)%ua_aexpr (Dcons (e1)%ua_eqn .. (Dcons (e2)%ua_eqn Dnil) ..) nil)
    (at level 90, right associativity) : Usuba_eqn.

Notation " var ':' typ" :=
    ({| VD_ID := (var)%string; VD_TYP := (typ)%ua_type ; VD_OPTS := nil |})
        (at level 70, no associativity) : Usuba_var_decl.

Notation "'node' name 'args' var_decl1 , .. , var_decl1b 'returns' var_decl2 , .. , var_decl2b 'vars' var_decl3 'let' x ; .. ; y 'tel'" :=
    {|
        ID := (name)%string;
        P_IN := (cons (var_decl1)%ua_var_decl .. (cons (var_decl1b)%ua_var_decl nil) ..)%ua_var_decl;
        P_OUT := (cons (var_decl2)%ua_var_decl .. (cons (var_decl2b)%ua_var_decl nil) ..)%ua_var_decl;
        OPT := No_opt;
        NODE := Single (var_decl3)%ua_var_decl (Dcons (x)%ua_eqn .. (Dcons (y)%ua_eqn Dnil) ..)
    |} (at level 90).

Notation "'table' name 'args' var_decl1 , .. , var_decl1b 'returns' var_decl2 , .. , var_decl2b 'let' x ; .. ; y 'tel' " :=
    {|
        ID := name;
        P_IN := (cons (var_decl1)%ua_var_decl .. (cons (var_decl1b)%ua_var_decl nil) ..)%ua_var_decl;
        P_OUT := (cons (var_decl2)%ua_var_decl .. (cons (var_decl2b)%ua_var_decl nil) ..)%ua_var_decl;
        OPT := No_opt;
        NODE := Table (cons x .. (cons y nil) ..)
    |} (at level 90).

Definition v8 : typ := Uint (Varslice (Id_s "D")) (Mvar (Id_s "m")) (Some 8).

Definition b1   : typ := Uint Bslice (Mint 1) (Some 1).
Definition b8   : typ := Uint Bslice (Mint 1) (Some 8).
Definition b16  : typ := Uint Bslice (Mint 1) (Some 16).
Definition b32  : typ := Uint Bslice (Mint 1) (Some 32).
Definition b64  : typ := Uint Bslice (Mint 1) (Some 64).
Definition b128 : typ := Uint Bslice (Mint 1) (Some 128).
Definition b256 : typ := Uint Bslice (Mint 1) (Some 256).
Definition b512 : typ := Uint Bslice (Mint 1) (Some 512).

Definition u1   : typ := Uint (Varslice (Id_s "d")) (Mint 1) None.
Definition u8   : typ := Uint (Varslice (Id_s "d")) (Mint 8) None.
Definition u16  : typ := Uint (Varslice (Id_s "d")) (Mint 16) None.
Definition u32  : typ := Uint (Varslice (Id_s "d")) (Mint 32) None.
Definition u32x2  : typ := Uint (Varslice (Id_s "d")) (Mint 32) (Some 2).
Definition u64  : typ := Uint (Varslice (Id_s "d")) (Mint  64) None.
Definition u128 : typ := Uint (Varslice (Id_s "d")) (Mint 128) None.
Definition u256 : typ := Uint (Varslice (Id_s "d")) (Mint 256) None.
Definition u512 : typ := Uint (Varslice (Id_s "d")) (Mint 512) None.


Definition input : string := "input".
Definition output : string := "output".
Definition out : string := "out".
Definition i : string := "i".
Definition o : string := "o".
Definition key : string := "key".
Definition plain : string := "plain".
Definition cipher : string := "cipher".
Definition tmp : string := "tmp".
Definition f : string := "f".
Definition round : string := "round".

Definition test : string := "test".
Definition a : string := "a".
Definition b : string := "b".

Definition node1 := node test args a : Nat returns b : Nat vars nil 
    let 
        ( b [ 1 ])%ua_var :: nil <:- ExpVar (Var a)
    tel.

Definition x : ident := "x"%string.
Definition y : ident := "y"%string.

Definition refresh : ident := "refresh"%string.

Definition f_node := node f args (x : Uint Vslice (Mint 32) None) returns (y: Uint Vslice (Mint 32) None) vars nil
    let
        Var y :: nil <:- ((x <<< 5) & Fun refresh (ECons x Enil)) xor (x <<< 1)
    tel.
