Require Import Bool.
Require Import PeanoNat.
From Usuba Require Import usuba_sem.

Definition ARCH_ADD_default  (d : dir) : option (nat -> nat -> nat) :=
    match d with
        _ => None
    end.
Definition ARCH_SUB_default  (d : dir) : option (nat -> nat -> nat) :=
    match d with
        _ => None
    end.
Definition ARCH_DIV_default  (d : dir) : option (nat -> nat -> nat) :=
    match d with
        _ => None
    end.
Definition ARCH_MOD_default  (d : dir) : option (nat -> nat -> nat) :=
    match d with
        _ => None
    end.
Definition ARCH_MUL_default  (d : dir) : option (nat -> nat -> nat) :=
    match d with
        _ => None
    end.

Fixpoint land (len n1 n2 : nat) :=
    match len with
    | 0 => 0
    | S len' =>
        let tl := land len' (n1 / 2) (n2 / 2) in
        if Nat.eqb (n1 mod 2) 1 && Nat.eqb (n2 mod 2) 1
        then 1 + tl * 2
        else tl * 2
    end.

Fixpoint lor (len n1 n2 : nat) :=
    match len with
    | 0 => 0
    | S len' =>
        let tl := lor len' (n1 / 2) (n2 / 2) in
        if Nat.eqb (n1 mod 2) 1 || Nat.eqb (n2 mod 2) 1
        then 1 + tl * 2
        else tl * 2
    end.

Fixpoint lxor (len n1 n2 : nat) :=
    match len with
    | 0 => 0
    | S len' =>
        let tl := lxor len' (n1 / 2) (n2 / 2) in
        if Bool.eqb (Nat.eqb (n1 mod 2) 1) (Nat.eqb (n2 mod 2) 1)
        then tl * 2
        else 1 + tl * 2
    end.
    
Definition ARCH_NOT_default  (d : dir) : option (nat -> nat) :=
    match d with
        _ => None
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
        _ => None
    end.

Definition ARCH_LSHIFT_default  (n : nat) (d : dir) : option (nat -> nat) :=
    match d with
        _ => None
    end.
Definition ARCH_RSHIFT_default  (n : nat) (d : dir) : option (nat -> nat) :=
    match d with
        _ => None
    end.
Definition ARCH_RASHIFT_default (n : nat) (d : dir) : option (nat -> nat) :=
    match d with
        _ => None
    end.
Definition ARCH_LROTATE_default (n : nat) (d : dir) : option (nat -> nat) :=
    match d with
        _ => None
    end.
Definition ARCH_RROTATE_default (n : nat) (d : dir) : option (nat -> nat) :=
    match d with
        _ => None
    end.

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