(*
Here b8[16] = b1[16][8] is represented as T16 (T8 Atom)
*)

Section Test.
Variables (Prod : Type -> Type -> Type).

Class Array (T : Type -> Type) := {
    MAP : forall A B, (A -> B) -> T A -> T B;
    pure : forall A, A -> T A;
    functor : forall A B, T (A -> B) -> T A -> T B;
    pair : forall A B, T A -> T B -> T (Prod A B)
}.

Class Indexable (T : Type -> Type) := {
    array : Array T;
    IndType : Type;
    lookup : (forall A, T A -> IndType -> A);
}.

Class Logic (A : Type) := {
    Not : A -> A;
    Xor : A -> A -> A;
    Or  : A -> A -> A;
    And : A -> A -> A;
    Andn: A -> A -> A;
}.

#[global]
Program Instance logic_array {A : Type} {T : Type -> Type} {AT : Array T} (LA : Logic A) : Logic (T A) := {
    Not := MAP _ _ Not;
    Xor  a b := functor _ _ (MAP _ _ Xor  a) b;
    Or   a b := functor _ _ (MAP _ _ Or   a) b;
    And  a b := functor _ _ (MAP _ _ And  a) b;
    Andn a b := functor _ _ (MAP _ _ Andn a) b;
}.

Variables (Atom : Type) (LAtom : Logic Atom).
Variables (T4 : Type -> Type) (IT4 : Indexable T4).
Variables (Build4 : forall A, A -> A -> A -> A -> T4 A).
Variables (I4a I4b I4c I4d : @IndType T4 _).
Variables (T8 : Type -> Type) (AT8 : Array T8).
Variables (T11 : Type -> Type) (IT11 : Indexable T11).
Variables (I11a I11b I11c I11d I11e I11f I11g I11h I11i I11j I11k : @IndType T11 _).
Variables (T16 : Type -> Type) (IT16 : Indexable T16).
Variables (T32 : Type -> Type).
Variables (T128 : Type -> Type) (AT128 : Array T128).

Variables
    (T32_split : forall A, T32 A -> T4 (T8 A))
    (T32_merge : forall A, T4 (T8 A) -> T32 A).
Variables
    (T128_split : forall A, T128 A -> T16 (T8 A))
    (T128_merge : forall A, T16 (T8 A) -> T128 A)
    (T128_split' : forall A, T128 A -> T4 (T32 A))
    (T128_merge' : forall A, T4 (T32 A) -> T128 A).

Variables (SubBytes_singles : forall A, T8 A -> T8 A).

Definition SubBytes : T16 (T8 Atom) -> T16 (T8 Atom) :=
    @MAP _ array _ _ (SubBytes_singles _).

Variables (Indexes : T16 (@IndType T16 _)).

Definition ShiftRows : T16 (T8 Atom) -> T16 (T8 Atom) :=
    fun el => @MAP _ array _ _ (lookup _ el) Indexes.

Variables (VectorTimes2 : T8 Atom -> T8 Atom).

Variables (ShiftL : nat -> T8 Atom -> T8 Atom).

Definition times2 : T8 Atom -> T8 Atom :=
    fun l => functor _ _ (MAP _ _ Xor (ShiftL 1 l)) (VectorTimes2 l).

Definition times3 : T8 Atom -> T8 Atom :=
    fun i => functor _ _ (MAP _ _ Xor (times2 i)) i.

Definition MixColumn_single : T4 (T8 Atom) -> T4 (T8 Atom) :=
    fun inp => Build4 _
        (Xor
            (Xor (times2 (lookup _ inp I4a)) (times3 (lookup _ inp I4b)))
            (Xor (lookup _ inp I4c) (lookup _ inp I4d))
        )
        (Xor
            (Xor (lookup _ inp I4a) (times2 (lookup _ inp I4b)))
            (Xor (times3 (lookup _ inp I4c)) (lookup _ inp I4d))
        )
        (Xor
            (Xor (lookup _ inp I4a) (lookup _ inp I4b))
            (Xor (times2 (lookup _ inp I4c)) (times3 (lookup _ inp I4d)))
        )
        (Xor
            (Xor (times3 (lookup _ inp I4a)) (lookup _ inp I4b))
            (Xor (lookup _ inp I4c) (times2 (lookup _ inp I4d)))
        ).

Definition MixColumn : T4 (T32 Atom) -> T4 (T32 Atom) :=
    fun inp =>
        Build4 _
            (T32_merge _ (MixColumn_single (T32_split _ (lookup _ inp I4a))))
            (T32_merge _ (MixColumn_single (T32_split _ (lookup _ inp I4b))))
            (T32_merge _ (MixColumn_single (T32_split _ (lookup _ inp I4c))))
            (T32_merge _ (MixColumn_single (T32_split _ (lookup _ inp I4d))))
        .

Definition AddRoundKey : T128 Atom -> T128 Atom -> T128 Atom :=
    fun i key => functor _ _ (MAP _ _ Xor i) key.

Definition AES : T128 Atom -> T11 (T128 Atom) -> T128 Atom :=
    fun plain key =>
        let tmp0 := AddRoundKey plain (lookup _ key I11a) in
        let tmp1 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp0))))))) (lookup _ key I11b) in
        let tmp2 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp1))))))) (lookup _ key I11c) in
        let tmp3 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp2))))))) (lookup _ key I11d) in
        let tmp4 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp3))))))) (lookup _ key I11e) in
        let tmp5 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp4))))))) (lookup _ key I11f) in
        let tmp6 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp5))))))) (lookup _ key I11g) in
        let tmp7 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp6))))))) (lookup _ key I11h) in
        let tmp8 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp7))))))) (lookup _ key I11i) in
        let tmp9 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp8))))))) (lookup _ key I11j) in
        AddRoundKey (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp9)))) (lookup _ key I11k)
    .


End Test.