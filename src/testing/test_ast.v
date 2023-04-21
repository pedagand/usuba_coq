Require Import String.
Require Import List.
Require Import ZArith.
Require Import Bool.
Require Import PeanoNat.
From mathcomp Require Import seq ssrnat.
From Usuba Require Import arch ident.
Require Import Lia.

Inductive log_op := And | Or | Xor | Andn.

Inductive arith_op := Add | Mul | Sub | Div | Mod.

Inductive shift_op := Lshift | Rshift | RAshift | Lrotate | Rrotate.

Inductive arith_expr : Type :=
    | Const_e : Z -> arith_expr
    | Var_e : ident -> arith_expr
    | Op_e : arith_op -> arith_expr -> arith_expr -> arith_expr.

Inductive dir := H | V | Var of string.

Definition size : Type := nat.

Definition dir_size : Type := dir * size.

Inductive typi := Array : typi -> nat -> typi | U : dir_size -> typi.

Inductive typ := I of typi | TArray : typ -> nat -> typ.

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

Fixpoint take_n {A n2} (n : nat) : vec A (n + n2) -> vec A n * vec A n2 :=
    match n return vec A (n + n2) -> vec A n * vec A n2 with
    | 0 => fun i => (vnil, i)
    | S n' => fun l => let (l1, l2) := take_n n' (tail l) in (@vcons _ (head l) n' l1, l2)
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

Inductive valuei : typi -> Type :=
    | Base (d : dir) (s : size) : Z -> valuei (U (d, s))
    | VIArray (t : typi) (l : nat) : Nat.lt 0 l -> vec (valuei t) l -> valuei (Array t l).

Inductive value : typ -> Type :=
    | ValueI (t : typi) : valuei t -> value (I t)
    | VArray (t : typ) (l : nat) : Nat.lt 0 l -> vec (value t) l -> value (TArray t l).

Inductive values : list typ -> Type :=
    | VLnil : values nil
    | VLcons {typ tl} : value typ -> values tl -> values (typ :: tl).

Definition valuei_vec {t l} (val : valuei (Array t l)) : vec (valuei t) l :=
    match val with VIArray _ _ _ vL => vL end.

Definition valuei_prop {t l} (val : valuei (Array t l)) : Nat.lt 0 l :=
    match val with VIArray _ _ p _ => p end.

Definition value_val {t} (val : value (I t)) : valuei t :=
    match val with ValueI _ v => v end.

Definition value_vec {t l} (val : value (TArray t l)) : vec (value t) l :=
    match val with VArray _ _ _ vL => vL end.

Definition value_prop {t l} (val : value (TArray t l)) : Nat.lt 0 l :=
    match val with VArray _ _ p _ => p end.

Definition values_hd {t tl} (v : values (t::tl)) : value t :=
    match v with VLcons _ _ h _ => h end.

Definition values_tl {t tl} (v : values (t::tl)) : values tl :=
    match v with VLcons _ _ _ t => t end.

Fixpoint values_app {t1 t2} : values t1 -> values t2 -> values (t1 ++ t2) :=
    match t1 return values t1 -> values t2 -> values (t1 ++ t2) with
    | nil => fun _ v => v
    | _::_ => fun v1 v2 => VLcons (values_hd v1) (values_app (values_tl v1) v2)
    end.

Fixpoint flatDS_typi (t : typi) : dir_size :=
    match t with
    | U ds => ds
    | Array t len => flatDS_typi t
    end.

Fixpoint flatL_typi (t : typi) : nat :=
    match t with
    | U ds => 1
    | Array t len => len * flatL_typi t
    end.

Fixpoint flatDS_typ (t : typ) : dir_size :=
    match t with
    | I ti => flatDS_typi ti
    | TArray t len => flatDS_typ t
    end.

Fixpoint flatL_typ (t : typ) : nat :=
    match t with
    | I ti => flatL_typi ti
    | TArray t len => len * flatL_typ t
    end.

Inductive typL_rel : list typ -> list typ -> Type :=
    | TRrefl : forall l, typL_rel l l
    | TRsym : forall l1 l2, typL_rel l1 l2 -> typL_rel l2 l1
    | TRtrans : forall l1 l2 l3, typL_rel l1 l2 -> typL_rel l2 l3 -> typL_rel l1 l3
    | TRrec : forall t l1 l2, typL_rel l1 l2 -> typL_rel (t::l1) (t::l2)
    | TRsimpl : forall t l, flatL_typ t <> 0 -> typL_rel (t :: l) (TArray (I (U (flatDS_typ t))) (flatL_typ t) :: l)
    | TRadd : forall t len1 len2 l, len1 <> 0 -> len2 <> 0 -> typL_rel (TArray t len1 :: TArray t len2 :: l) (TArray t (len1 + len2) :: l)
    | TRone : forall t l, typL_rel (t :: l) (TArray t 1 :: l)
    .

Fixpoint convert_simpli {ti} : valuei ti ->  vec (valuei (U (flatDS_typi ti))) (flatL_typi ti) :=
    match ti return valuei ti -> vec (valuei (U (flatDS_typi ti))) (flatL_typi ti) with
    | U ds => fun v => vcons v vnil
    | Array ti' l => fun v => flat (map (@convert_simpli ti') (valuei_vec v))
    end.

Fixpoint convert_simpl {t} : value t ->  vec (value (I (U (flatDS_typ t)))) (flatL_typ t) :=
    match t return value t -> vec (value (I (U (flatDS_typ t)))) (flatL_typ t) with
    | I ti => fun v => map (ValueI _) (convert_simpli (value_val v))
    | TArray t' l => fun v => flat (map (@convert_simpl t') (value_vec v))
    end.

Fixpoint to_vec_vec {A} (l n : nat) : vec A (n * l) -> vec (vec A l) n :=
    match n return vec A (n * l) -> vec (vec A l) n with
    | 0 => fun v => vnil
    | S n' => fun vL => let (hd, tl) := take_n l vL in @vcons _ hd n' (to_vec_vec _ _ tl)
    end.

Lemma prop_zero_contr1 {l1 l2}:
    l1 * l2 <> 0 -> l1 <> 0.
Proof.
    intros Abs HEq; apply Abs.
    rewrite HEq; clear.
    rewrite mul0n; reflexivity.
Defined.

Lemma not_zero_lt_0 {n}:
    n <> 0 -> Nat.lt 0 n.
Proof.
    lia.
Defined.

Lemma prop_zero_contr2 {l1 l2}:
    l1 * l2 <> 0 -> l2 <> 0.
Proof.
    intros Abs HEq; apply Abs.
    rewrite HEq; clear.
    rewrite muln0; reflexivity.
Defined.

Definition unwrap_vI {t} (v : value (I t)) : valuei t :=
    match v with
    | ValueI _ v => v
    end.

Fixpoint convert_simpli_inv {ti} : (flatL_typi ti <> 0) -> vec (valuei (U (flatDS_typi ti))) (flatL_typi ti) -> valuei ti :=
    match ti return (flatL_typi ti <> 0) -> vec (valuei (U (flatDS_typi ti))) (flatL_typi ti) -> valuei ti with
    | U ds => fun _ v => head v
    | Array ti' l => fun p v => VIArray _ _ (not_zero_lt_0 (prop_zero_contr1 p)) (map (@convert_simpli_inv ti' (prop_zero_contr2 p)) (to_vec_vec _ _ v))
    end.

Fixpoint convert_simpl_inv {t} : (flatL_typ t <> 0) -> vec (value (I (U (flatDS_typ t)))) (flatL_typ t) -> value t :=
    match t return (flatL_typ t <> 0) -> vec (value (I (U (flatDS_typ t)))) (flatL_typ t) -> value t with
    | I ti => fun p v => ValueI _ (convert_simpli_inv p (map unwrap_vI v))
    | TArray t' l => fun p v =>
        VArray _ _ (not_zero_lt_0 (prop_zero_contr1 p))
            (map (@convert_simpl_inv t' (prop_zero_contr2 p)) (to_vec_vec _ _ v))
    end.

Lemma valuei_imp_not_zero ti:
    valuei ti -> flatL_typi ti <> 0.
Proof.
    induction ti as [ti HRec len|ds]; simpl.
    2: lia.
    intro v; inversion v as [|t' len' SupZero val].
    clear H0 H1 len' t'.
    destruct val as [|h l _]; [> inversion SupZero | idtac].
    pose (p := HRec h); generalize p; clear.
    destruct flatL_typi.
    + intro H; exfalso; apply H; reflexivity.
    + intro; rewrite mulSn; rewrite addSn; discriminate.
Defined.

Lemma value_imp_not_zero t:
    value t -> Nat.lt 0 (flatL_typ t).
Proof.
    intro v.
    assert (flatL_typ t <> 0).
    2: lia.
    generalize v; clear.
    induction t as [ti|t HRec len]; simpl.
    {
        intro v; inversion v as [vi|].
        apply valuei_imp_not_zero; assumption.
    }
    intro v; inversion v as [|t' len' SupZero val].
    clear H0 H1 len' t'.
    destruct val as [|h l _]; [> inversion SupZero | idtac].
    pose (p := HRec h); generalize p; clear.
    destruct flatL_typ.
    + intro H; exfalso; apply H; reflexivity.
    + intro; rewrite mulSn; rewrite addSn; discriminate.
Defined.

Lemma add_lt_0 {n1 n2}:
        Nat.lt 0 n1 -> Nat.lt 0 (n1 + n2).
Proof.
    intro H; inversion H; [> rewrite add1n | rewrite addSn].
    all: lia.
Defined.

Lemma lt_0_1: Nat.lt 0 1. Proof. lia. Qed.

Fixpoint convert_values {l1 l2} (p : typL_rel l1 l2) : values l1 -> values l2 :=
    match p as p' in typL_rel l1 l2 return values l1 -> values l2 with
        | TRrefl l => fun i => i
        | TRsym _ _ p => convert_values_inv p
        | TRtrans _ _ _ p1 p2 => fun v => convert_values p2 (convert_values p1 v)
        | TRrec _ _ _ p => (fun v => VLcons (values_hd v) (convert_values p (values_tl v)))
        | TRsimpl _ _ _ => (fun v => VLcons (VArray _ _ (value_imp_not_zero _ (values_hd v)) (convert_simpl (values_hd v))) (values_tl v))
        | TRadd _ _ _ _ _ _ => (fun v => VLcons (VArray _ _ (add_lt_0 (value_prop (values_hd v))) (append (value_vec (values_hd v)) (value_vec (values_hd (values_tl v))))) (values_tl (values_tl v)))
        | TRone _ _ => (fun v => VLcons (VArray _ _ lt_0_1 (vcons (values_hd v) vnil)) (values_tl v))
    end
with convert_values_inv {l1 l2} (p : typL_rel l1 l2) : values l2 -> values l1 :=
    match p as p' in typL_rel l1 l2 return values l2 -> values l1 with
    | TRrefl l => fun i => i
    | TRsym _ _ p => convert_values p
    | TRtrans _ _ _ p1 p2 => fun v => convert_values_inv p1 (convert_values_inv p2 v)
    | TRrec _ _ _ p => (fun v => VLcons (values_hd v) (convert_values_inv p (values_tl v)))
    | TRsimpl _ _ nz => (fun v => VLcons (convert_simpl_inv nz (value_vec (values_hd v))) (values_tl v))
    | TRadd _ _ _ _ nz1 nz2 => (fun v =>
        let (t1, t2) := take_n _ (value_vec (values_hd v)) in
        VLcons (VArray _ _ (not_zero_lt_0 nz1) t1) (VLcons (VArray _ _ (not_zero_lt_0 nz2) t2) (values_tl v)))
    | TRone _ _ => (fun v => VLcons (head (value_vec (values_hd v))) (values_tl v))
    end.

Inductive binop := Aop of arith_op | Lop of log_op.

Inductive monop :=
    | NotOp : monop
    | Sop : shift_op -> nat -> monop.

Inductive op := B of binop | M of monop.

Fixpoint find_val {A : Type} (ctxt : list (ident * A)) (i : ident) : option A :=
    match ctxt with
        | nil => None
        | ((name, val)::tl) =>
            if ident_beq i name
            then Some val
            else find_val tl i
    end.

Definition ctxt : Type := list (ident * typ).

Class not_base (t : typ) := { DIFF_I := forall t2, t = I t2 -> False }.

#[global]
Program Instance not_basep (t : typ) (l : nat) : not_base (TArray t l).

Fixpoint valid_index (t : typ) (i : nat) : Prop :=
    match t with
    | I _ => False
    | TArray (I _) l => Nat.lt i l
    | TArray t' _ => valid_index t' i
    end.

Fixpoint index_on (t : typ) : typ :=
    match t with
    | I _ => t (* should not happen *)
    | TArray (I t') _ => I t'
    | TArray t' l => TArray (index_on t') l
    end.

Fixpoint indexes_on (t : typ) (n : nat) : typ :=
    match t with
    | I _ => t (* should not happen *)
    | TArray (I t') _ => I (Array t' n)
    | TArray t' l => TArray (indexes_on t' n) l
    end.

Inductive var (tctxt : ctxt) : typ -> Type :=
    | VIdent (i : ident) (t : typ) : find_val tctxt i = Some t -> var tctxt t
    | Index {t : typ} (v : var tctxt t) (i : nat) : valid_index t i -> var tctxt (index_on t)
    (* | Range {t : typ} {_ : not_base t} (v : var tctxt t) (a1 a2 : nat) : var tctxt (indexes_on t (a2 + 1 - a1)) *)
    | Slice {t : typ} (v : var tctxt t) (iL : list nat) : iL <> nil -> Forall (valid_index t) iL -> var tctxt (indexes_on t (length iL))
    .

Inductive expr (A : op -> typ -> Prop) (tctxt : ctxt) : list typ -> Type :=
    | Const (d : dir) (s : size) (z : Z) : expr A tctxt [:: I (U (d, s))]
    | ExpVar {t : typ} (v : var tctxt t) : expr A tctxt [:: t]
    | Monop {t : typ} (o : monop) (tc : A (M o) t) (e : expr A tctxt [:: t]) : expr A tctxt [:: t]
    | Binop {t : typ} (o : binop) (tc : A (B o) t) (e1 e2 : expr A tctxt [:: t]) : expr A tctxt [:: t]
    | Tuple {t : list typ} (e : list_expr A tctxt t) : expr A tctxt t
    | ECoercion {t1 t2 : list typ} : typL_rel t1 t2 -> expr A tctxt t1 -> expr A tctxt t2
with list_expr (A : op -> typ -> Prop) (tctxt : ctxt) : list typ -> Type :=
    | LEnil : list_expr A tctxt nil
    | LEcons {l1 l2} : expr A tctxt l1 -> list_expr A tctxt l2 -> list_expr A tctxt (l1 ++ l2)
    .

Definition context (types : ctxt) := forall (i : ident) (t : typ), find_val types i = Some t -> value t.

Fixpoint lifti_bop {t} (op : binop) {struct t} : valuei t -> valuei t -> valuei t :=
    match t return valuei t -> valuei t -> valuei t with
    (* | Nat => (fun v1 v2 => match v1 with end) *)
    | Array t l => (fun v1 v2 => VIArray t l (valuei_prop v1) (map2 (lifti_bop op) (valuei_vec v1) (valuei_vec v2)))
    | U (d, s) => (fun v1 v2 =>
        match v1 with
        | Base _ _ z1 => match v2 with
            | Base _ _ z2 => match op with
                | Aop Add  => Base d s (add_fun s z1 z2)
                | Aop Sub  => Base d s (sub_fun s z1 z2)
                | Aop Mul  => Base d s (mul_fun s z1 z2)
                | Aop Mod  => Base d s (mod_fun s z1 z2)
                | Aop Div  => Base d s (div_fun s z1 z2)
                | Lop And  => Base d s (land  s z1 z2)
                | Lop Or   => Base d s (lor   s z1 z2)
                | Lop Xor  => Base d s (lxor  s z1 z2)
                | Lop Andn => Base d s (landn s z1 z2)
                end
            end
        end)
    end.

Fixpoint lift_bop {t} (op : binop) {struct t} : value t -> value t -> value t :=
    match t return value t -> value t -> value t with
    | TArray t l => (fun v1 v2 => VArray t l (value_prop v1) (map2 (lift_bop op) (value_vec v1) (value_vec v2)))
    | I ti => (fun v1 v2 => ValueI _ (lifti_bop op (value_val v1) (value_val v2)))
    end.

Fixpoint lifts_bop {t} (op : binop) {struct t} : values t -> values t -> values t :=
    match t return values t -> values t -> values t with
    | nil => (fun _ _ => VLnil)
    | t::tl => (fun v1 v2 => VLcons (lift_bop op (values_hd v1) (values_hd v2))
                                    (lifts_bop op (values_tl v1) (values_tl v2)))
    end.

Fixpoint lifti_mop {t} (op : monop) {struct t} : valuei t -> valuei t :=
    match t return valuei t -> valuei t with
    (* | Nat => (fun v => match v with end) *)
    | Array t l => (fun v => VIArray t l (valuei_prop v) (map (lifti_mop op) (valuei_vec v)))
    | U (d, s) => (fun v =>
        match v with
        | Base _ _ z => match op with
            | NotOp => Base d s (lnot s z)
            | Sop _ _ => Base d s z
            end
        end)
    end.

Fixpoint lift_mop {t} (op : monop) {struct t} : value t -> value t :=
    match t return value t -> value t with
    | TArray t l => (fun v => VArray t l (value_prop v) (map (lift_mop op) (value_vec v)))
    | I ti => (fun v => ValueI _ (lifti_mop op (value_val v)))
    end.

Fixpoint lifts_mop {t} (op : monop) {struct t} : values t -> values t :=
    match t return values t -> values t with
    | nil => (fun _ => VLnil)
    | t::tl => (fun v => VLcons (lift_mop op (values_hd v))
                                    (lifts_mop op (values_tl v)))
    end.

Lemma abs_S_le_0: forall i, (S i <= 0)%coq_nat -> False.
Proof.
    intros i Hle.
    inversion Hle as [H|].
Defined.

Lemma simpl_add1: forall i n, (S (S i) <= S n)%coq_nat -> (S i <= n)%coq_nat.
Proof.
    lia.
Defined.

Fixpoint nth {A n} (i : nat) (soundness : (S i <=  n)%coq_nat) (l : vec A n) : A :=
    match l as l' in vec _ n return (S i <= n)%coq_nat -> A with
    | vcons hd _ tl => (match i with
        | 0 => fun p => hd
        | S i' => fun p => nth i' (simpl_add1 _ _ p) tl
        end)
    | vnil => (fun p => match abs_S_le_0 _ p with end)
    end soundness.

Definition get_proof (t : typi) (l i : nat) (p : valid_index (TArray (I t) l) i) : Nat.lt i l := p.

Definition get_index_inner {t i l} (v : value (TArray t l)) : Nat.lt i l -> value t :=
    match v as v' in value (TArray t l) return Nat.lt i l -> value t with
    | VArray _ _ _ els => fun p => nth i p els
    end.

Fixpoint nthL {A l} (iL : list nat) (soundness : Forall (fun i => Nat.lt i l) iL) (els : vec A l) : vec A (length iL) :=
    match iL return Forall (fun i => Nat.lt i l) iL -> vec A (length iL) with
    | nil => fun _ => vnil
    | i :: tl => fun p => vcons (nth i (Forall_inv p) els) (nthL tl (Forall_inv_tail p) els)
    end soundness.

Definition get_index_innerL {t iL l} (v : value (TArray t l)) : Forall (fun i => Nat.lt i l) iL -> vec (value t) (length iL) :=
    match v as v' in value (TArray t l) return Forall (fun i => Nat.lt i l) iL -> vec (value t) (length iL) with
    | VArray _ _ _ els => fun p => nthL iL p els
    end.

Fixpoint get_index {t} (i : nat) {struct t} : valid_index t i -> value t -> value (index_on t) :=
    match t return valid_index t i -> value t -> value (index_on t) with
    | I ti => fun vi _ => match vi with end
    | TArray t' l =>
        match t' return (valid_index t' i -> value t' -> value (index_on t'))
            -> valid_index (TArray t' l) i -> value (TArray t' l) -> value (index_on (TArray t' l)) with
        | I _ => fun _ vi v => get_index_inner v vi
        | TArray t' l => fun f vi v => match v as v' in value (TArray t' l) return (value t' -> value (index_on t')) -> value (TArray (index_on t') l) with
            | VArray _ len p els => fun f => VArray _ len p (map f els)
            end (f vi)
        end (@get_index t' i)
    end.

Lemma not_empty_not_zero_length {A} :
    forall iL : list A, iL <> nil -> Nat.lt 0 (length iL).
Proof.
    intro iL; destruct iL; simpl.
    + intro H; exfalso; apply H; reflexivity.
    + lia.
Defined.

Fixpoint get_indexes {t} (iL : list nat) {struct t} : iL <> nil -> (Forall (valid_index t) iL) -> value t -> value (indexes_on t (length iL)) :=
    match t return iL <> nil -> Forall (valid_index t) iL -> value t -> value (indexes_on t (length iL)) with
    | I ti => match iL return iL <> nil -> Forall (valid_index (I ti)) iL -> value (I ti) -> value (indexes_on (I ti) (length iL)) with
        | nil => fun abs => match abs eq_refl with end
        | hd :: _ => fun _ hforall => match (Forall_inv hforall) with end
    end
    | TArray t' l =>
        fun not_empty_iL => match t' return (Forall (valid_index t') iL -> value t' -> value (indexes_on t' (length iL)))
            -> Forall (valid_index (TArray t' l)) iL -> value (TArray t' l) -> value (indexes_on (TArray t' l) (length iL)) with
        | I _ => fun _ vi v => ValueI _ (VIArray _ _ (not_empty_not_zero_length _ not_empty_iL) (map unwrap_vI (get_index_innerL v vi)))
        | TArray t' l => fun f vi v => match v as v' in value (TArray t' l) return (value t' -> value (indexes_on t' (length iL))) -> value (TArray (indexes_on t' (length iL)) l) with
            | VArray _ len p els => fun f => VArray _ len p (map f els)
            end (f vi)
        end (@get_indexes t' iL not_empty_iL)
    end.


Fixpoint eval_var {types t} (ctxt : context types) (var : var types t) : value t :=
    match var with
    | VIdent i t p => ctxt i t p
    | Index _ var i vi => get_index i vi (eval_var ctxt var)
    | Slice _ var iL ne vi => get_indexes iL ne vi (eval_var ctxt var) 
    end.

Fixpoint eval_expr {arch types t} (ctxt : context types) (e : expr arch types t) : values t :=
    match e with
    | Const _ _ z =>  VLcons (ValueI _ (Base _ _ z)) VLnil
    | ExpVar _ v => VLcons (eval_var ctxt v) VLnil
    | Monop _ o _ e => lifts_mop o (eval_expr ctxt e)
    | @Binop _ _ t o _ e1 e2 => lifts_bop o (eval_expr ctxt e1) (eval_expr ctxt e2)
    | Tuple _ eL => eval_list_expr ctxt eL
    | ECoercion _ _ tr e => convert_values tr (eval_expr ctxt e)
    end
with eval_list_expr {arch types t} (ctxt : context types) (eL : list_expr arch types t) : values t :=
    match eL as eL' in list_expr _ _ t return values t with
    | LEnil => VLnil
    | LEcons _ _ hd tl => values_app (eval_expr ctxt hd) (eval_list_expr ctxt tl)
    end.

Section Testing.

Variables (tctxt : ctxt).
Variables (p : find_val tctxt (Num 0) = Some (TArray (TArray (I (Array (U (H, 8)) 3)) 4) 5)).

Lemma util1: Nat.lt 3 4. Proof. lia. Defined.

Definition v : var tctxt (TArray (I (Array (U (H, 8)) 3)) 5) :=
    (Index _ (VIdent _ (Num 0) _ p) 3 util1).

End Testing.

Fixpoint Ai (o : op) (ti : typi) : Prop :=
    match ti with
    | U (d, s) => match d, o, s with
        | H, B (Aop Add), 8 => True
        | _, _, _ => False
        end
    | Array ti' _ => Ai o ti'
    end.

Fixpoint A (o : op) (t : typ) : Prop :=
    match t with
    | I ti => Ai o ti
    | TArray t' _ => A o t'
    end.

Definition tctxt : ctxt := (Num 0, TArray (I (U (H, 8))) 3) :: (Num 1, TArray (I (U (H, 8))) 5) :: nil.

Lemma util2a:
    find_val tctxt (Num 0) = Some (TArray (I (U (H, 8))) 3).
Proof. simpl; reflexivity. Defined.

Lemma util2a':
    find_val tctxt (Num 1) = Some (TArray (I (U (H, 8))) 5).
Proof. simpl; reflexivity. Defined.

Lemma util2b:
    valid_index (TArray (I (U (H, 8))) 3) 0.
Proof. simpl; lia. Defined.

Lemma util2c:
    valid_index (TArray (I (U (H, 8))) 3) 2.
Proof. simpl; lia. Defined.

Lemma util2c':
    Forall (valid_index (TArray (I (U (H, 8))) 5)) [:: 0; 4].
Proof.
    constructor; simpl; [> lia | idtac].
    constructor; simpl; [> lia | constructor].
Defined.

Lemma util2d:
    A (B (Aop Add)) (TArray (I (U (H, 8))) 2).
Proof. simpl; constructor. Defined.

Lemma util2e:
    typL_rel (I (U (H, 8)) :: I (U (H, 8)) :: nil)  [:: TArray (I (U (H, 8))) 2].
Proof.
    refine (TRtrans _ _ _ _ _).
    2: apply (TRadd _ 1 _ _).
    2,3: lia.
    refine (TRtrans _ _ _ _ _).
    1: apply TRone.
    apply TRrec.
    apply TRone.
Defined.

Lemma util2e':
    typL_rel (I (Array (U (H, 8)) 2)::nil)  [:: TArray (I (U (H, 8))) 2].
Proof.
    refine (TRsimpl _ _ _ ).
    simpl.
    rewrite muln1.
    discriminate.
Defined.

Lemma nempty {A} {h : A} {l} : h :: l <> nil.
Proof. discriminate. Qed. 

Definition e : expr A tctxt (TArray (I (U (H, 8))) 2 :: nil) :=
    Binop _ _ (Aop Add) util2d
        (ECoercion _ _ util2e (Tuple A _ (LEcons _ _ (ExpVar _ _ (Index _ (VIdent _ (Num 0) _ util2a) 0 util2b)) (LEcons _ _ (ExpVar _ _ (Index _ (VIdent _ (Num 0) _ util2a) 2 util2c)) (LEnil _ _)))))
        (ECoercion _ _ util2e' (ExpVar _ _ (Slice _ (VIdent _ (Num 1) _ util2a') (0 :: 4 :: nil) nempty util2c'))).
