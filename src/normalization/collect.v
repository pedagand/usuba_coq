From Usuba Require Import usuba_AST.
From Coq Require Import MSets.
Require Import Coq.Structures.OrdersEx.

Module iset := Make String_as_OT.

Fixpoint collect_aexpr (e : arith_expr) : iset.t :=
    match e with
    | Var_e i => iset.singleton i
    | Const_e _ => iset.empty
    | Op_e _ e1 e2 => iset.union (collect_aexpr e1) (collect_aexpr e2)
    end.

Fixpoint collect_aexprl (e : list arith_expr) : iset.t :=
    match e with
    | nil => iset.empty
    | h :: tl => iset.union (collect_aexpr h) (collect_aexprl tl)
    end.

Function collect_var (v : var) : iset.t :=
    match v with
    | Var var => iset.singleton var
    | Index v i => iset.union (collect_var v) (collect_aexpr i)
    | Range v s e => iset.union (collect_var v) (iset.union (collect_aexpr s) (collect_aexpr e))
    | Slice v el => iset.union (collect_var v) (collect_aexprl el)
    end.

Fixpoint collect_varl (vl : list var) : iset.t :=
    match vl with
    | nil => iset.empty
    | v :: tl => iset.union (collect_var v) (collect_varl tl)
    end.

Function collect_expr (e : expr) : iset.t :=
    match e with
    | Const _ _ => iset.empty
    | ExpVar v => collect_var v
    | Tuple el => collect_exprl el
    | Not e => collect_expr e
    | Log _ e1 e2 | Arith _ e1 e2 => iset.union (collect_expr e1) (collect_expr e2)
    | Shift _ expr aexpr => iset.union (collect_expr expr) (collect_aexpr aexpr)
    | Shuffle v _ => collect_var v
    | Bitmask expr aexpr => iset.union (collect_expr expr) (collect_aexpr aexpr)
    | Pack e1 e2 _ => iset.union (collect_expr e1) (collect_expr e2)
    | Fun f exprl => iset.union (iset.singleton f) (collect_exprl exprl)
    | Fun_v f aexpr exprl => iset.union (iset.singleton f) (iset.union (collect_aexpr aexpr) (collect_exprl exprl))
    end
with collect_exprl el :=
    match el with
    | Enil => iset.empty
    | ECons e el => iset.union (collect_expr e) (collect_exprl el)
    end.

Function collect_vdecl (p : p) : iset.t :=
    match p with
    | nil => iset.empty
    | v :: tl => iset.add (VD_ID v) (collect_vdecl tl)
    end.

Function collect_deq (d : deq) : iset.t :=
    match d with
    | Eqn v e _ => iset.union (collect_varl v) (collect_expr e)
    | Loop i aei1 aei2 eqns opt =>
        iset.add i (iset.union 
            (iset.union (collect_aexpr aei1) (collect_aexpr aei2)) (collect_deqs eqns))
    end
with collect_deqs (dl : list_deq) : iset.t :=
    match dl with
    | Dnil => iset.empty
    | Dcons hd tl => iset.union (collect_deq hd) (collect_deqs tl)
    end.

Function collect_bounddeq (d : deq) : iset.t :=
    match d with
    | Eqn v e _ => (collect_varl v)
    | Loop i aei1 aei2 eqns opt =>
        iset.add i (collect_bounddeqs eqns)
    end
with collect_bounddeqs (dl : list_deq) : iset.t :=
    match dl with
    | Dnil => iset.empty
    | Dcons hd tl => iset.union (collect_bounddeq hd) (collect_bounddeqs tl)
    end.
