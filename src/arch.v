Require Import Bool.
Require Import ZArith.
Require Import List.
From Usuba Require Import usuba_AST.

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

Definition IntSize : Type := nat.
Definition IntSize_beq := Nat.eqb.

Definition IntSize_of_nat (n : nat) : option IntSize := Some n.

Inductive dir :=
    | DirH : IntSize -> dir
    | DirV : IntSize -> dir
    | DirB
    | DirUnknow
    | DirH_
    | DirV_
    | Dir_S : IntSize -> dir.
Scheme Equality for dir.

(* Fixpoint to_bits (len n : nat) : list bool :=
    match len with
    | 0 => nil
    | S len' =>
        (Nat.eqb (n mod 2) 1)::to_bits len' (n / 2)
    end.

Fixpoint from_bits (l : list bool) : nat :=
    match l with
    | nil => 0
    | hd::tl => (if hd then 1 else 0) + 2 * from_bits tl
    end.

Definition chop (len n : nat) :=
    from_bits (to_bits len n). *)

Definition arith_wrapper {A : Type} (arch : dir -> bool) (op : nat -> A) (d : dir) : option A :=
    if arch d
    then
        match d with
        | DirV i | DirH i => Some (op i)
        | DirB => Some (op 1)
        | _ => None
        end
    else None.

(* Fixpoint extend (len a : nat) : nat :=
    match len with
    | 0 => 1
    | S len' => (a mod 2) + 2 * extend len' (a / 2)
    end. *)

Definition add_fun (len : nat) (a b : Z) : Z := (a + b) mod (2 ^ (Z.of_nat len)).
Definition sub_fun (len : nat) (a b : Z) : Z := (a - b) mod (2 ^ (Z.of_nat len)).
Definition mod_fun (_   : nat) (a b : Z) : Z := (a mod b).
Definition div_fun (_   : nat) (a b : Z) : Z := (a / b).
Definition mul_fun (len : nat) (a b : Z) : Z := (a * b) mod (2 ^ (Z.of_nat len)).

Fixpoint map2 {A B C : Type} (f : A -> B -> C) l1 l2 : list C :=
    match (l1, l2) with
    | (nil, _) | (_, nil) => nil
    | (h1::t1, h2::t2) => f h1 h2::map2 f t1 t2
    end. 


Definition lnot (len : nat) (n : Z) : Z := Z.lxor n ((2 ^Z.of_nat len) - 1).

Definition land (len : nat) (n1 n2 : Z) : Z := Z.land n1 n2.

Definition lor   (len : nat) (n1 n2 : Z) : Z := Z.lor n1 n2.
Definition lxor  (len : nat) (n1 n2 : Z) : Z := Z.lxor n1 n2.
Definition landn (len : nat) (n1 n2 : Z) : Z := Z.land n1 (lnot len n2).

Definition lshift (len s : nat) (nb : Z) : Z := (nb * 2 ^ (Z.of_nat s)) mod (2 ^ Z.of_nat len).

Goal
    lshift 8 3 129 = 8%Z.
Proof. cbn. reflexivity. Qed.

Definition rshift (len s : nat) (nb : Z) : Z := nb / (2 ^ (Z.of_nat s)).

(* Definition rashift (len s nb : nat) :=
    let l := (to_bits len nb) in
    let lst := last l false in
    match take_n s l with
    | None => 0
    | Some (l1, l2) =>
        from_bits (map (fun _ => lst) l2 ++ l1)
    end. *)
    
Definition lrotate (len s : nat) (nb : Z) : Z := 
    Z.lor (lshift len s nb) (rshift len (len - s) nb).
Definition rrotate (len s : nat) (nb : Z) :
    Z := Z.lor (rshift len s nb) (lshift len (len - s) nb).

Definition shift_wrapper (param : dir -> nat -> bool) (op : shift_op) (n : nat) (d : dir) (i : Z) : option Z :=
    if param d n
    then
        op <- match op with
            | Lshift  => Some lshift
            | Rshift  => Some rshift
            | RAshift => None
            | Rrotate => Some rrotate
            | Lrotate => Some lrotate
        end;
        match d with
        | DirB => Some (op 1 n i)
        | DirH len | DirV len => Some (op len n i)
        | _ => None
        end
    else None.

Record architecture : Type := {
    IMPL_ARITH : dir -> bool;
    IMPL_LOG : dir -> bool;
    IMPL_SHIFT : dir -> nat -> bool;
}.

Definition default_arch : architecture := {|
    IMPL_ARITH := fun d =>
        match d with
        | DirV 8 | DirV 16 | DirV 32 | DirV 64 => true
        | _ => false
        end;
        
    IMPL_LOG := fun d =>
        match d with
        | DirV _ | DirH _ | DirB => true
        | _ => false
        end;

    IMPL_SHIFT := fun d s =>
        match d with
        | DirH 2 => Nat.ltb s 2
        | DirH 4 => Nat.ltb s 4
        | DirH 8 => Nat.ltb s 8
        | DirV 16 | DirH 16 => Nat.ltb s 16
        | DirV 32 | DirH 32 => Nat.ltb s 32
        | DirV 64 | DirH 64 => Nat.ltb s 64
        | _ => false
        end
|}.
