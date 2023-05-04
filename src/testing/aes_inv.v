(*
Here b8[16] is represented as T8 (T16 Atom)
*)

Section Test.

Class Array (T : Type -> Type) := {
    MAP : forall A B, (A -> B) -> T A -> T B;
    pure : forall A, A -> T A;
    functor : forall A B, T (A -> B) -> T A -> T B;
}.

Class Indexable (T : Type -> Type) := {
    array : Array T;
    IndType : Type;
    lookup : (forall A, T A -> IndType -> A);
}.

Definition comp (f g : Type -> Type) : Type -> Type := fun a => f (g a).

Notation "f 'o' g" :=
    (comp f g)
    (at level 50, left associativity).

#[global]
Program Instance array_comp {U V : Type -> Type} {AU : Array U} {AV : Array V} : Array (U o V) := {
    MAP A B f := @MAP U AU (V A) (V B) (@MAP V AV A B f);
    pure A v := @pure U AU (V A) (@pure V AV A v);
    functor A B f := @functor U AU (V A) (V B) (@MAP U _ _ _ (functor _ _) f);
}.

#[global]
Program Instance proj_index {T : Type -> Type} (C : Indexable T) : Array T := array.

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
Variables (T8 : Type -> Type) (IT8 : Indexable T8).
Variables (T11 : Type -> Type) (IT11 : Indexable T11).
Variables (I11a I11b I11c I11d I11e I11f I11g I11h I11i I11j I11k : @IndType T11 _).
Variables (T16 : Type -> Type) (IT16 : Indexable T16).
Variables (I16a I16b I16c I16d I16e I16f I16g I16h
           I16i I16j I16k I16l I16m I16n I16o I16p : @IndType T16 _).

Variables (Build16 : forall A,
                A -> A -> A -> A -> 
                A -> A -> A -> A -> 
                A -> A -> A -> A -> 
                A -> A -> A -> A -> T16 A).
Variables (T32 : Type -> Type) (IT32 : Indexable T32).
Variables (T128 : Type -> Type) (AT128 : Array T128).

Variables
(T32_split : forall A, T32 A -> T8 (T4 A))
(T32_merge : forall A, T8 (T4 A) -> T32 A).
Variables
(T128_split : forall A, T128 A -> T8 (T16 A))
(T128_merge : forall A, T8 (T16 A) -> T128 A)
(T128_split' : forall A, T128 A -> T32 (T4 A))
(T128_merge' : forall A, T32 (T4 A) -> T128 A).

Variables (SubBytes_singles : forall A, T8 A -> T8 A).

Variables (IndexesT16 : T16 (@IndType T16 _)).

Definition SubBytes (l : T8 (T16 Atom)) : T8 (T16 Atom) :=
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
        (pure _ (Build16 _))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16a) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16b) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16c) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16d) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16e) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16f) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16g) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16h) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16i) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16j) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16k) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16l) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16m) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16n) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16o) l)))
        (SubBytes_singles _ (MAP _ _ (fun l' => lookup _ l' I16p) l)))
    .

Variables (Indexes : T16 (@IndType T16 _)).

Definition ShiftRows : T8 (T16 Atom) -> T8 (T16 Atom) :=
    MAP _ _ (fun l => MAP _ _ (lookup _ l) Indexes).

Variables (VectorTimes2 : T8 Atom -> T8 Atom).

Variables (ShiftL : nat -> T8 Atom -> T8 Atom).

Definition times2 : T8 Atom -> T8 Atom :=
    fun l => functor _ _ (MAP _ _ Xor (ShiftL 1 l)) (VectorTimes2 l).

Definition times3 : T8 Atom -> T8 Atom :=
    fun i => functor _ _ (MAP _ _ Xor (times2 i)) i.

Definition MixColumn_single : (T8 o T4) Atom -> (T8 o T4) Atom :=
    fun inp =>
    (functor _ _
    (functor _ _
    (functor _ _
    (functor _ _
        (@pure _ array _ (Build4 _))
        (Xor
            (Xor (times2 (MAP _ _ (fun l => lookup _ l I4a) inp)) (times3 (MAP _ _ (fun l => lookup _ l I4b) inp)))
            (Xor (MAP _ _ (fun l => lookup _ l I4c) inp) (MAP _ _ (fun l => lookup _ l I4d) inp))
        ))
        (Xor
            (Xor (MAP _ _ (fun l => lookup _ l I4a) inp) (times2 (MAP _ _ (fun l => lookup _ l I4b) inp)))
            (Xor (times3 (MAP _ _ (fun l => lookup _ l I4c) inp)) (MAP _ _ (fun l => lookup _ l I4d) inp))
        ))
        (Xor
            (Xor (MAP _ _ (fun l => lookup _ l I4a) inp) (MAP _ _ (fun l => lookup _ l I4b) inp))
            (Xor (times2 (MAP _ _ (fun l => lookup _ l I4c) inp)) (times3 (MAP _ _ (fun l => lookup _ l I4d) inp)))
        ))
        (Xor
            (Xor (times3 (MAP _ _ (fun l => lookup _ l I4a) inp)) (MAP _ _ (fun l => lookup _ l I4b) inp))
            (Xor (MAP _ _ (fun l => lookup _ l I4c) inp) (times2 (MAP _ _ (fun l => lookup _ l I4d) inp)))
        )).

Definition MixColumn : (T32 o T4) Atom -> (T32 o T4) Atom :=
    fun inp =>
        (functor _ _
        (functor _ _
        (functor _ _
        (functor _ _
            (@pure _ array _ (Build4 _))
            (T32_merge _ (MixColumn_single (T32_split _ (MAP _ _ (fun l => lookup _ l I4a) inp)))))
            (T32_merge _ (MixColumn_single (T32_split _ (MAP _ _ (fun l => lookup _ l I4b) inp)))))
            (T32_merge _ (MixColumn_single (T32_split _ (MAP _ _ (fun l => lookup _ l I4c) inp)))))
            (T32_merge _ (MixColumn_single (T32_split _ (MAP _ _ (fun l => lookup _ l I4d) inp)))))
        .

Definition AddRoundKey : T128 Atom -> T128 Atom -> T128 Atom :=
    fun i key => functor _ _ (MAP _ _ Xor i) key.

Definition AES : T128 Atom -> (T128 o T11) Atom -> T128 Atom :=
    fun plain key =>
        let tmp0 := AddRoundKey plain (MAP _ _ (fun k => lookup _ k I11a) key) in
        let tmp1 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp0))))))) (MAP _ _ (fun k => lookup _ k I11b) key) in
        let tmp2 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp1))))))) (MAP _ _ (fun k => lookup _ k I11c) key) in
        let tmp3 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp2))))))) (MAP _ _ (fun k => lookup _ k I11d) key) in
        let tmp4 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp3))))))) (MAP _ _ (fun k => lookup _ k I11e) key) in
        let tmp5 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp4))))))) (MAP _ _ (fun k => lookup _ k I11f) key) in
        let tmp6 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp5))))))) (MAP _ _ (fun k => lookup _ k I11g) key) in
        let tmp7 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp6))))))) (MAP _ _ (fun k => lookup _ k I11h) key) in
        let tmp8 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp7))))))) (MAP _ _ (fun k => lookup _ k I11i) key) in
        let tmp9 := AddRoundKey (T128_merge' _ (MixColumn (T128_split' _ (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp8))))))) (MAP _ _ (fun k => lookup _ k I11j) key) in
        AddRoundKey (T128_merge _ (ShiftRows (SubBytes (T128_split _ tmp9)))) (MAP _ _ (fun k => lookup _ k I11k) key)
    .

End Test.