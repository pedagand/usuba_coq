Require Import Arith_base.
Import EqNotations.
Require Import ZArith.

(* From mathcomp Require Import all_ssreflect. *)

From Usuba Require Import ident arch usuba_AST usuba_sem arch.


Inductive vec (A : Type) : nat -> Type :=
    | vnil : vec A 0
    | vcons (a : A) (n : nat) (v : vec A n) : vec A (S n).

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

Fixpoint append {A} {n m} (l1 : vec A n) (l2 : vec A m) : vec A (n + m) :=
    match l1 with
    | vnil => l2
    | vcons hd _ tl => vcons hd (append tl l2)
    end.

Fixpoint flat {A} {n m} (l : vec (vec A m) n) : vec A (n * m) :=
    match l with
    | vnil => vnil
    | vcons hd _ tl => append hd (flat tl)
    end. 

Fixpoint map2 {A B C} (f : A -> B -> C) {n} (l1 : vec A n) (l2 : vec B n) : vec C n :=
    match l1 as l1' in vec _ n return vec B n -> vec C n with
    | vnil => (fun _ => vnil)
    | vcons h1 _ t1 => (fun l2 => vcons (f h1 (head l2)) (map2 f t1 (tail l2)))
    end l2.

(* Fixpoint coerce (l1 l2 : list nat) : list nat :=
    match l1 with
    | nil => nil
    | h1::t1 => match l2 with
        | h2::t2 => if Nat.eqb h1 h2
            then h1::coerce t1 t2
            else prod_list l1::nil
        | _ => prod_list l1::nil
        end
    end. *)

Class flatten (A : Type) (len : nat) := {
    ELS : A -> vec Z len
}.

#[global]
Instance flatten_Z : flatten Z 1 := {
    ELS z := vcons z vnil;
}.

#[global]
Program Instance flatten_Vec (A : Type) (len n : nat) (F : flatten A len) : flatten (vec A n) (n * len) := {
    ELS l := flat (map ELS l);
}.

Class diff (a b : nat) := { p := a <> b }.

#[global]
Program Instance diff_0S {n} : diff 0 (S n).

#[global]
Program Instance diff_S0 {n} : diff (S n) 0.

#[global]
Program Instance diff_SS {n1 n2} {d : diff n1 n2} : diff (S n1) (S n2).

Class eval_aop (A B C : Type) (a : arith_op) (d : dir) := { EVAL_AOP : A -> B -> C }.

#[global]
Program Instance eval_aop_vec_same {A B C : Type} {n : nat} {op : arith_op} {d : dir} {EA : eval_aop A B C op d} : eval_aop (vec A n) (vec B n) (vec C n) op d := {
    EVAL_AOP l1 l2 := @map2 A B C EVAL_AOP n l1 l2
}.

#[global]
Program Instance eval_aop_base : eval_aop Z Z Z Add (DirV 16) := {
    EVAL_AOP := add_fun 16
}.

Goal
    @EVAL_AOP _ _ _ Add (DirV 16) _ (vcons (vcons 3%Z vnil) vnil) (vcons (vcons 4%Z vnil) vnil) = vcons (vcons 7%Z vnil) vnil.
Proof.
    simpl; unfold add_fun; cbn; reflexivity.
Qed.

#[global]
Program Instance eval_aop_vec_diff {A B : Type} {nA nB : nat} {op : arith_op} {d : dir} {op_tc : eval_aop Z Z Z op d}
    {len : nat}
    {fA : flatten (vec A nA) len} {fB : flatten (vec B nB) len}
    {p : diff nA nB}
        : eval_aop (vec A nA) (vec B nB) (vec Z len) op d := {
    EVAL_AOP l1 l2 := map2 (@EVAL_AOP Z Z Z op d op_tc) (ELS l1) (ELS l2)
}.

Definition t : flatten (vec Z 2) 2.
Proof.
    pose (p := flatten_Vec Z 1 2).
    simpl in p.
    apply p.
    apply flatten_Z.
Qed.

Definition util:
    flatten (vec Z 2) 2.
Proof.
    pose (p := flatten_Vec Z 1 2 _).
    simpl in p.
    exact p.
Defined.

Definition util':
    flatten (vec (vec Z 2) 1) 2.
Proof.
    pose (p := flatten_Vec (vec Z 2) 2 1 util).
    simpl in p.
    exact p.
Defined.

Goal
    @EVAL_AOP _ _ _ Add (DirV 16) (@eval_aop_vec_diff _ _ _ _ _ _ _ _ util util' _) (vcons 4%Z (vcons 3%Z vnil)) (vcons (vcons 4%Z (vcons 1%Z vnil)) vnil) = vcons 8%Z (vcons 4%Z vnil).
Proof.
    cbn; reflexivity.
Qed.

Inductive vari :=
    | Ident : ident -> vari
    | Index : vari -> nat -> vari
    | Range : vari -> nat -> nat -> vari
    | Slice : vari -> list nat -> vari.

Inductive typei :=
    | U : dir -> typei 
    | TIA : typei -> nat -> typei.

Inductive typeo :=
    | I : typei -> typeo
    | TOA : typeo -> nat -> typeo.

Definition type_ctxt := list (ident * typei).

Fixpoint typeo_of_typei (t : typei) : typeo :=
    match t with
    | U d => I (U d)
    | TIA t l => TOA (typeo_of_typei t) l
    end.

Axiom get_indexes : vari -> typei -> typeo.

Lemma infer_base (i : ident) (t : typei) : get_indexes (Ident i) t = (typeo_of_typei t).
Proof. admit. Admitted.

Lemma infer_lift v ti (l : nat)
    : get_indexes v (TIA ti l) = (TOA (get_indexes v ti) l).
Proof. admit. Admitted.

Lemma infer_index v ti1 ti2 (l i : nat) (c : get_indexes v ti1 = (I ti2))
    : get_indexes (Index v i) (TIA ti1 l) = (I ti2).
Proof. admit. Admitted.

Lemma infer_range v ti1 ti2 (l a1 a2 : nat) (c : get_indexes v ti1 = (I ti2))
    : get_indexes (Range v a1 a2) (TIA ti1 l) = (I (TIA ti2 (a2 + 1 - a1))).
Proof. admit. Admitted.

Lemma infer_slice v ti1 ti2 (l : nat) (iL : list nat) (c : get_indexes v ti1 = (I ti2))
    : get_indexes (Slice v iL) (TIA ti1 l) = (I (TIA ti2 (length iL))).
Proof. admit. Admitted.

Goal
    forall i,
    get_indexes
        (Index (Range (Index (Ident i) 0) 1 2) 3)
        (TIA (TIA (TIA (TIA (U DirB) 5) 6) 7) 8)
        = (TOA (I (TIA (U DirB) 2)) 8).
Proof.
    intro.
    rewrite infer_lift; f_equal.
    apply infer_index.
    refine (infer_range _ _ _ _ _ _ _).
    apply infer_index.
    apply infer_base.
Qed.

