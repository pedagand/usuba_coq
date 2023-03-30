From Usuba Require Import usuba_AST.
Require Import String.
Require Import List.

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
Coercion Const_e : nat >-> arith_expr.
Coercion Var : ident >-> var.

Notation "x '&' y" := (Log And (x)%ua_expr (y)%ua_expr) (at level 87, left associativity) : Usuba_expr.
Notation "x 'xor' y" := (Log Xor (x)%ua_expr (y)%ua_expr) (at level 87, left associativity) : Usuba_expr.
Notation "x '<<' y" := (Shift Lshift (x)%ua_expr (y)%ua_aexpr) (at level 87, left associativity) : Usuba_expr.
Notation "x '>>' y" := (Shift Rshift (x)%ua_expr (y)%ua_aexpr) (at level 87, left associativity) : Usuba_expr.
Notation "x '<<<' y" := (Shift Lrotate (x)%ua_expr (y)%ua_aexpr) (at level 87, left associativity) : Usuba_expr.
Notation "x '>>>' y" := (Shift Rrotate (x)%ua_expr (y)%ua_aexpr) (at level 87, left associativity) : Usuba_expr.

Notation "v '[' e ']'" := (Index (v)%ua_var (e)%ua_aexpr) (at level 88, left associativity) : Usuba_var.

Notation "a '<=' b ';' tl" := (Dcons (Eqn (a)%ua_var (b)%ua_expr false) tl)
    (at level 90, right associativity) : Usuba_eqn.

Notation "a '<:=' b ';' tl" := (Dcons (Eqn (a)%ua_var (b)%ua_expr true) tl)
    (at level 90, right associativity) : Usuba_eqn.
    
Notation "a '<:=' b ';'" := (a <:= b ; Dnil)%ua_eqn
    (at level 89, no associativity) : Usuba_eqn.
(* Notation "a '<=' b ';'" := (a <= b ; Dnil)%ua_eqn
    (at level 89, no associativity) : Usuba_eqn. *)

Notation "hd ',' tl" :=
    ((hd)%ua_var_decl ++ (tl)%ua_var_decl)
        (at level 90, right associativity) : Usuba_var_decl.

Notation " var ':' typ" :=
    ({| VD_ID := (var)%string; VD_TYP := (typ)%ua_type ; VD_OPTS := nil |}::nil)
        (at level 89, no associativity) : Usuba_var_decl.

Notation "'node' name 'args' var_decl 'returns' var_decl2 'vars' var_decl3 'let' eqns 'tel'" :=
    {|
        ID := name;
        P_IN := (var_decl)%ua_var_decl;
        P_OUT := (var_decl2)%ua_var_decl;
        OPT := No_opt;
        NODE := Single (var_decl3)%ua_var_decl (eqns)%ua_eqn
    |} (at level 90).

Definition test : string := "test".
Definition a : string := "a".
Definition b : string := "b".

Definition node1 := node test args (a : Nat) returns (b : Nat) vars nil 
    let (Var b [ Const_e 1 ])%ua_var :: nil <:= ExpVar (Var a); tel.

Definition f : ident := "f"%string.
Definition x : ident := "x"%string.
Definition y : ident := "y"%string.

Definition refresh : ident := "refresh"%string.

Definition f_node := node f args (x : Uint Vslice (Mint 32) 1) returns (y: Uint Vslice (Mint 32) 1) vars nil
    let
        Var y :: nil <:= ((x <<< 5) & Fun refresh (ECons x Enil)) xor (x <<< 1);
    tel.

Print f_node.

