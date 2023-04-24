Require Import String.
Require Import List.
Require Import ZArith.
Require Import Bool.
Require Import PeanoNat.
From mathcomp Require Import seq ssrnat.
Require Import Lia.

Inductive log_op := And | Or | Xor | Andn.

Inductive arith_op := Add | Mul | Sub | Div | Mod.

Inductive shift_op := Lshift | Rshift | RAshift | Lrotate | Rrotate.

Inductive binop := Aop of arith_op | Lop of log_op.

Inductive monop :=
    | NotOp : monop
    | Sop : shift_op -> nat -> monop.

Inductive op := B of binop | M of monop.

Section AST.

(* Permet de décrire les entiers *)
Variables (base : Type).

(* On prend un type T, notre type des types *)
Variables (T : Type).

(*
On prend un foncteur de concrétisation qui permet d'aller de
notre espace des types vers notre espace des valeurs
*)
Variables (Val : T -> Type).

(*
On défini ici un autre foncteur pour passer d'une list de types à aux valeurs correspondantes

Ce foncteur préserve les opérations:
- nil
- cons
- hd
- tl
- app
*)
Inductive Values : list T -> Type :=
    | Vnil : Values nil
    | Vcons : forall t tl, Val t -> Values tl -> Values (t :: tl).

Definition Values_hd {t tl} (v : Values (t::tl)) : Val t :=
    match v with Vcons _ _ h _ => h end.

Definition Values_tl {t tl} (v : Values (t::tl)) : Values tl :=
    match v with Vcons _ _ _ t => t end.

Definition Vals : forall t, Val t -> Values [:: t] :=
    (fun _ v => Vcons _ _ v Vnil).

Fixpoint appValues (t1 t2 : list T) {struct t1} : Values t1 -> Values t2 -> Values (t1 ++ t2) :=
    match t1 return Values t1 -> Values t2 -> Values (t1 ++ t2) with 
    | nil => fun _ l2 => l2
    | hd::tl => fun l1 l2 => Vcons _ _ (Values_hd l1) (appValues _ _ (Values_tl l1) l2)
    end.

(* On prend un foncteur des types vers le types des variables de ce type *)
Variables (ident : T -> Type).

(* Ici on pose une relation sur les types ainsi qu'un ppcm *)
Variables (Trel : list T -> list T -> Prop)
    (convert : forall l1 l2, Trel l1 l2 -> Values l1 -> Values l2)
    (ppcm : forall l1 l2, Trel l1 l2 -> list T)
    (ppcm_rel1 : forall (l1 l2 : list T) (r:Trel l1 l2), Trel l1 (ppcm l1 l2 r))
    (ppcm_rel2 : forall (l1 l2 : list T) (r:Trel l1 l2), Trel l2 (ppcm l1 l2 r))
    .

Arguments convert {_} {_} _ _.
Arguments ppcm {_} {_} _.
Arguments ppcm_rel1 {_} {_} _.
Arguments ppcm_rel2 {_} {_} _.

Variables (U : base -> T) (Build : Z -> forall b : base, Val (U b)).

(*
    On pose Array n un endofoncteur de notre catégorie des types
    ce foncteur préserve les morphismes :
    - map
    - map2
    mais doit aussi avoir une section get_ind
*)
Variables (Array : nat -> T -> T)
    (map : forall A B n, (Val A -> Val B) -> Val (Array n A) -> Val (Array n B))
    (map2 : forall A B C n, (Val A -> Val B -> Val C) -> Val (Array n A) -> Val (Array n B) -> Val (Array n C))
    (get_ind : forall A (n i : nat), (i < n)%coq_nat -> Val (Array n A) -> Val A) (* TODO add security on i *)
    (map_ind : forall A n (iL : list nat), Forall (fun i => (i < n)%coq_nat) iL -> Val (Array n A) -> Val (Array (length iL) A))
    .

(*
    Types class pour l'indiçage
*)
Class Indexing (depth : nat) (t : T) (i : nat) := {
    INDEX : T;
    GET_INDEX : Val t -> Val INDEX;
}.

Class IndexingL (depth : nat) (t : T) (i : list nat) := {
    INDEXES : T;
    GET_INDEXES : Val t -> Val INDEXES;
}.

#[global]
Program Instance liftIndexBase (t : T) (n i : nat) (p : (i < n)%coq_nat) : Indexing 0 (Array n t) i := {
    INDEX := t;
    GET_INDEX l := get_ind t n i p l
}.

#[global]
Program Instance liftIndex (depth : nat) (t : T) (n i : nat) (it : Indexing (S depth) t i) : Indexing (depth) (Array n t) i := {
    INDEX := Array n INDEX;
    GET_INDEX l := map _ _ _ GET_INDEX l
}.

#[global]
Program Instance liftIndexL (depth : nat) (t : T) (n: nat) (i : list nat) (it : IndexingL (S depth) t i) : IndexingL depth (Array n t) i := {
    INDEXES := Array n INDEXES;
    GET_INDEXES l := map _ _ _ GET_INDEXES l
}.

#[global]
Program Instance liftIndexLBase (t : T) (n: nat) (i : list nat) (ip : Forall (fun j => (j < n)%coq_nat) i) : IndexingL 0 (Array n t) i := {
    INDEXES := Array (length i) t;
    GET_INDEXES l := map_ind _ _ _ ip l
}.

(*
    Type class pour les operateurs
*)
Class ArchImplM (A : T) (o : monop) := {
    OPEM : Val A -> Val A;
}.

Class ArchImplML (A : list T) (o : monop) := {
    OPEML : Values A -> Values A;
}.

Class ArchImplB (A : T) (o : binop) := {
    OPEB : Val A -> Val A -> Val A;
}.

Class ArchImplBL (A : list T) (o : binop) := {
    OPEBL : Values A -> Values A -> Values A;
}.

#[global]
Program Instance listAIM (A : T) (n : nat) (o : monop) (tc : ArchImplM A o) : ArchImplM (Array n A) o := {
    OPEM := map _ _ _ OPEM
}.

#[global]
Program Instance listAIB (A : T) (n : nat) (o : binop) (tc : ArchImplB A o) : ArchImplB (Array n A) o := {
    OPEB := map2 _ _ _ _ OPEB
}.

#[global]
Program Instance listAIMLnil (o : monop) : ArchImplML nil o := {
    OPEML l := l
}.

#[global]
Program Instance listAIML (A : T) (AL : list T) (o : monop) (tc : ArchImplM A o) (tcL : ArchImplML AL o) : ArchImplML (A :: AL) o := {
    OPEML l := Vcons _ _ (OPEM (Values_hd l)) (OPEML (Values_tl l))
}.

#[global]
Program Instance listAIBLnil (o : binop) : ArchImplBL nil o := {
    OPEBL l1 l2 := Vnil
}.

#[global]
Program Instance listAIBL (A : T) (AL : list T) (o : binop) (tc : ArchImplB A o) (tcL : ArchImplBL AL o) : ArchImplBL (A :: AL) o := {
    OPEBL l1 l2 := Vcons _ _ (OPEB (Values_hd l1) (Values_hd l2))
                                    (OPEBL (Values_tl l1) (Values_tl l2))
}.

(*
    Définition des variables
*)
Inductive var : T -> Type :=
    | VIdent {t : T} : ident t -> var t
    | Index {t : T} (v : var t) (depth i : nat) {ind : Indexing depth t i} : var (@INDEX _ _ _ ind)
    | Slice {t : T} (v : var t) (depth : nat) (i : list nat) {ind : IndexingL depth t i} : var (@INDEXES _ _ _ ind)
    .

(*
    Définition des expressions
*)
Inductive expr : list T -> Type :=
    | Const (b : base) : Z -> expr [:: U b]
    | ExpVar {t : T} : var t -> expr [:: t]
    | Binop {t1 t2 : list T} (r : Trel t1 t2) (o : binop) : ArchImplBL (ppcm r) o -> expr t1 -> expr t2 -> expr (ppcm r)
    | Monop {t : T} (o : monop) : ArchImplM t o -> expr [:: t] -> expr [:: t]
    | Tuple {t : list (list T)} : list_expr t -> expr (flatten t)
    (* | Coerce {t t' : T} (_ : Val t -> Val t') : expr t -> expr t' *)
with list_expr : list (list T) -> Type :=
    | LEnil : list_expr nil
    | LEcons {hd tl} : expr hd -> list_expr tl -> list_expr (hd :: tl)
    .

Fixpoint eval_var {t} (ctxt : forall t, ident t -> Val t) (v : var t) : Val t :=
    match v as v' in var t return Val t with
    | VIdent _ i => ctxt _ i
    | Index _ v i ind => @GET_INDEX _ _ ind (eval_var ctxt v)
    | Slice _ v iL ind => @GET_INDEXES _ _ ind (eval_var ctxt v)
    end.

Fixpoint eval_expr {t : list T} (ctxt : forall t, ident t -> Val t) (e : expr t) : Values t :=
    match e with
    | Const b z => Vals _ (Build z b)
    | ExpVar _ v => Vals _ (eval_var ctxt v)
    | Binop t1 t2 r op tc e1 e2 => OPEBL (convert (ppcm_rel1 _) (eval_expr ctxt e1)) (convert (ppcm_rel2 _) (eval_expr ctxt e2))
    | Monop _ op tc e => OPEML (eval_expr ctxt e)
    | Tuple _ el => eval_list_expr ctxt el
    (* | Coerce _ _ f e => f (eval_expr ctxt e) *)
    end
with eval_list_expr {t} (ctxt : forall t, ident t -> Val t) (e : list_expr t) : Values (flatten t) :=
    match e with
    | LEnil => Vnil
    | LEcons _ _ e el => appValues _ _ (eval_expr ctxt e) (eval_list_expr ctxt el)
    end.

End AST.


(*
    Quelques tests sur l'AST défini si dessus
*)
Section Testing1.


Inductive vec (A : Type) : nat -> Type :=
    | vnil : vec A 0
    | vcons (h : A) {n : nat} : vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ {_} _.

Definition head {A n} (v : vec A (S n)) : A :=
  match v with
    | vcons a _ _ => a
  end.

Definition tail {A n} (v : vec A (S n)) : vec A n :=
  match v with
    | vcons _ _ t => t
  end.

Fixpoint map {A B} (f : A -> B) {n} (l : vec A n) : vec B n :=
    match l with
    | vnil => vnil
    | vcons hd _ tl => vcons (f hd) (map f tl)
    end.

Fixpoint map2 {A B C} (f : A -> B -> C) {n} (l1 : vec A n) (l2 : vec B n) : vec C n :=
    match l1 as l1' in vec _ n return vec B n -> vec C n with
    | vnil => (fun _ => vnil)
    | vcons h1 _ t1 => (fun l2 => vcons (f h1 (head l2)) (map2 f t1 (tail l2)))
    end l2.

Inductive dir := H | V | Var of string.

Definition size : Type := nat.

Definition dir_size : Type := dir * size.

Inductive typ := TArray : typ -> nat -> typ | U : dir_size -> typ.

Inductive value : typ -> Type :=
    | Base (_ : Z) (ds : dir_size) : value (U ds)
    | VArray (t : typ) (l : nat) : vec (value t) l -> value (TArray t l).

From Usuba Require Import arch.

Definition Z_of_value {ds} (v : value (U ds)) : Z :=
    match v with
    | Base z _ => z
    end.

Instance archm_H8_not : ArchImplM _ value (U (H, 8)) NotOp := {
    OPEM v := Base (lnot 8 (Z_of_value v)) _
}.

Instance archm_H8_add : ArchImplB _ value (U (H, 8)) (Aop Add) := {
    OPEB v1 v2 := Base (add_fun 8 (Z_of_value v1) (Z_of_value v2)) _
}.

Definition typ_rel := @eq (list typ).
Definition ppcm : forall (l1 l2 : list typ), typ_rel l1 l2 -> list typ := fun i _ _ => i.
Definition convert : forall (l1 l2 : list typ), typ_rel l1 l2 -> Values _ value l1 -> Values _ value l2.
Proof.
    intros l1 l2 H.
    unfold typ_rel in H.
    destruct H.
    exact (fun i => i).
Defined.

Definition ppcm_rel1 : forall (l1 l2 : list typ) (r : typ_rel l1 l2), typ_rel l1 (ppcm l1 l2 r).
Proof.
    intros l1 l2 ->; unfold ppcm; reflexivity.
Defined.

Definition ppcm_rel2 : forall (l1 l2 : list typ) (r : typ_rel l1 l2), typ_rel l2 (ppcm l1 l2 r).
Proof.
    intros l1 l2 ->; unfold ppcm; reflexivity.
Defined.

Definition e : expr dir_size _ value value typ_rel ppcm U [:: U (H, 8)] :=
    Const _ _ _ _ _ _ _ _ 3.

Definition e' : expr dir_size _ value value typ_rel ppcm U [:: U (H, 8)] :=
    Monop _ _ _ _ _ _ _ NotOp _ (Const _ _ _ _ _ _ _ _ 3).

Goal eval_expr _ _ _ _ _ convert _ ppcm_rel1 ppcm_rel2 _ Base (fun _ i => i) e' = Vcons _ _ _ _ (Base 252 (H, 8)) (Vnil _ _).
Proof.
    simpl.
    reflexivity.
Qed.

Goal ppcm [:: U (H, 8)] [:: U (H, 8)] eq_refl = [:: U (H, 8)].
Proof.
    unfold ppcm; reflexivity.
Qed.

Definition e3 : expr dir_size _ value value typ_rel ppcm U [:: U (H, 8)] :=
    Binop _ _ _ _ _ ppcm U eq_refl (Aop Add) _
        (Const _ _ _ _ _ _ _ _ 3)
        (Const _ _ _ _ _ _ _ _ 5).

Goal eval_expr _ _ _ _ _ convert _ ppcm_rel1 ppcm_rel2 _ Base (fun _ t => t) e3 = Vcons _ _ _ _ (Base 8 (H, 8)) (Vnil _ _).
Proof.
    cbn.
    reflexivity.
Qed.

End Testing1.


