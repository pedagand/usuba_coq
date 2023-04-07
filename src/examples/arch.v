Require Import Bool.
Require Import PeanoNat.
Require Import List.
From Usuba Require Import usuba_sem.


Fixpoint to_bits (len n : nat) : list bool :=
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
    from_bits (to_bits len n).

Definition arith_default (op : nat -> nat -> nat) (d : dir) : option (nat -> nat -> nat) :=
    match d with
    | DirV  8 => Some (fun a b => chop  8 (op a b))
    | DirV 16 => Some (fun a b => chop 16 (op a b))
    | DirV 32 => Some (fun a b => chop 32 (op a b))
    | DirV 64 => Some (fun a b => chop 64 (op a b))
    | _ => None
end.

Definition ARCH_ADD_default : dir -> option (nat -> nat -> nat) :=
    arith_default (Nat.add).

Definition ARCH_SUB_default : dir -> option (nat -> nat -> nat) :=
    arith_default (Nat.sub).
Definition ARCH_DIV_default : dir -> option (nat -> nat -> nat) :=
    arith_default (Nat.div).
Definition ARCH_MOD_default : dir -> option (nat -> nat -> nat) :=
    arith_default (Nat.modulo).
Definition ARCH_MUL_default : dir -> option (nat -> nat -> nat) :=
    arith_default (Nat.mul).

Fixpoint map2 {A B C : Type} (f : A -> B -> C) l1 l2 : list C :=
    match (l1, l2) with
    | (nil, _) | (_, nil) => nil
    | (h1::t1, h2::t2) => f h1 h2::map2 f t1 t2
    end. 

Definition lnot (len n : nat) : nat :=
    from_bits (map negb (to_bits len n)).

Definition land (len n1 n2 : nat) : nat :=
    from_bits (map2 andb (to_bits len n1) (to_bits len n2)).

Definition lor (len n1 n2 : nat) : nat :=
    from_bits (map2 orb (to_bits len n1) (to_bits len n2)).

Definition lxor (len n1 n2 : nat) : nat :=
    from_bits (map2 xorb (to_bits len n1) (to_bits len n2)).

Definition landn (len n1 n2 : nat) : nat :=
    from_bits (map2 (fun a b => a && (negb b)) (to_bits len n1) (to_bits len n2)).

Definition ARCH_NOT_default  (d : dir) : option (nat -> nat) :=
    match d with
        | DirH l => Some (lnot l)
        | DirV l => Some (lnot l)
        | DirB => Some (lnot 1)
        | _ => None
    end.

Definition ARCH_AND_default  (d : dir) : option (nat -> nat -> nat) :=
    match d with
        | DirH l => Some (land l)
        | DirV l => Some (land l)
        | DirB => Some (land 1)
        | _ => None
    end.

Definition ARCH_OR_default   (d : dir) : option (nat -> nat -> nat) :=
    match d with
        | DirH l => Some (lor l)
        | DirV l => Some (lor l)
        | DirB => Some (lor 1)
        | _ => None
    end.

Definition ARCH_XOR_default  (d : dir) : option (nat -> nat -> nat) :=
    match d with
        | DirH l => Some (lxor l)
        | DirV l => Some (lxor l)
        | DirB => Some (lxor 1)
        | _ => None
    end.

Definition ARCH_ANDN_default (d : dir) : option (nat -> nat -> nat) :=
    match d with
        | DirH l => Some (landn l)
        | DirV l => Some (landn l)
        | DirB => Some (landn 1)
        | _ => None
    end.

Definition shift_default (op : nat -> nat -> nat -> nat) (n : nat) (d : dir) : option (nat -> nat) :=
    match d with
    | DirB => if Nat.ltb n 1
        then Some (op 1 n)
        else None
    | DirH len | DirV len => if Nat.ltb n len
        then Some (op len n)
        else None
    | _ => None
    end.

Definition lshift (len s nb : nat) :=
    match take_n (len - s) (to_bits len nb) with
    | None => 0
    | Some (l1, l2) => from_bits (map (fun _ => false) l2 ++ l1)
    end.

Goal
    lshift 8 3 129 = 8.
Proof. cbn. reflexivity. Qed.

Definition rshift (len s nb : nat) :=
    match take_n s (to_bits len nb) with
    | None => 0
    | Some (l1, l2) => from_bits (map (fun _ => false) l2 ++ l1)
    end.

Definition rashift (len s nb : nat) :=
    let l := (to_bits len nb) in
    let lst := last l false in
    match take_n s l with
    | None => 0
    | Some (l1, l2) =>
        from_bits (map (fun _ => lst) l2 ++ l1)
    end.
    
Definition lrotate (len s nb : nat) :=
    match take_n (len - s) (to_bits len nb) with
    | None => 0
    | Some (l1, l2) => from_bits (l2 ++ l1)
    end.

Definition rrotate (len s nb : nat) :=
    match take_n s (to_bits len nb) with
    | None => 0
    | Some (l1, l2) => from_bits (l2 ++ l1)
    end.
    
Definition ARCH_LSHIFT_default : nat -> dir -> option (nat -> nat) :=
    shift_default lshift.

Definition ARCH_RSHIFT_default : nat -> dir -> option (nat -> nat) :=
    shift_default rshift.

Definition ARCH_RASHIFT_default : nat -> dir ->option (nat -> nat) :=
    shift_default rashift.

Definition ARCH_LROTATE_default : nat -> dir -> option (nat -> nat) :=
    shift_default lrotate.

Definition ARCH_RROTATE_default : nat -> dir -> option (nat -> nat) :=
    shift_default rrotate.

Definition default_arch : architecture := {|
    ARCH_ADD := ARCH_ADD_default;
    ARCH_SUB := ARCH_SUB_default;
    ARCH_DIV := ARCH_DIV_default;
    ARCH_MOD := ARCH_MOD_default;
    ARCH_MUL := ARCH_MUL_default;

    ARCH_NOT  := ARCH_NOT_default;
    ARCH_AND  := ARCH_AND_default;
    ARCH_OR   := ARCH_OR_default;
    ARCH_XOR  := ARCH_XOR_default;
    ARCH_ANDN := ARCH_ANDN_default;

    ARCH_LSHIFT  := ARCH_LSHIFT_default;
    ARCH_RSHIFT  := ARCH_RSHIFT_default;
    ARCH_RASHIFT := ARCH_RASHIFT_default;
    ARCH_LROTATE := ARCH_LROTATE_default;
    ARCH_RROTATE := ARCH_RROTATE_default;
|}.
