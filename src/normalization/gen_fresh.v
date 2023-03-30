From Usuba Require Import usuba_AST collect.
From Coq Require Import String.
From Coq Require Import PeanoNat.
From Coq Require Import MSetFacts.
Require Import Lia.

Lemma String_append_length:
    forall (s1 s2 : string),
        String.length (s1 ++ s2)%string = String.length s1 + String.length s2.
Proof.
    intros s1 s2; induction s1; simpl.
    + reflexivity.
    + rewrite IHs1; reflexivity.
Qed.

Lemma leb_add_1_l:
    forall n, n + 1 <=? n  = false.
Proof.
    induction n; simpl; auto.
Qed.

Fixpoint fill (name : string) (size : nat) : string :=
    match size with
    | 0 => name ++ "'"
    | S size => fill (name ++ "'") size
    end.

Fixpoint fresh_name_inner (fuel : nat) (size : nat) (name : ident) (s : iset.t) : (ident * nat * iset.t) :=
    match fuel with
    | 0 => 
        let name2 := fill name (size - String.length name) in
        (name2, max (String.length name + 1) (size + 1), iset.add name2 s)
    | S fuel' => match iset.mem name s with
        | true => fresh_name_inner fuel' size (name ++ "'")%string s
        | false => (name, Nat.max (String.length name) size, iset.add name s)
        end
    end.

Definition var_set : Type := nat * iset.t.

Definition var_set_ok (vs : var_set) : Prop :=
    let (size, vars) := vs in
        forall name, iset.mem name vars = true -> String.length name <= size.

Definition fresh_name (name : ident) (vs : var_set) : (ident * var_set):=
    let (size, vars) := vs in
    let (name_size, vars') := fresh_name_inner 1000 size name vars in
    let (name', size') := name_size in
    (name', (size', vars')).

Lemma fill_soundness:
    forall s name,
        String.length (fill name s) = String.length name + s + 1.
Proof.
    induction s as [|s HRec]; simpl; intro. 
    + rewrite String_append_length; simpl; lia.
    + rewrite HRec; rewrite String_append_length; simpl; lia.
Qed.

Theorem fresh_name_inner_soundness:
    forall fuel size s name s2 name2 size2,
        var_set_ok (size, s) ->
        fresh_name_inner fuel size name s = (name2, size2, s2) ->
            iset.mem name2 s = false /\ iset.mem name2 s2 = true /\
            var_set_ok (size2, s2).
Proof.
    unfold var_set_ok.
    induction fuel as [|fuel' HRec]; simpl.
    all: intros size s name s2 name2 size2 HLength.
    {
        intro HEq; inversion HEq.
        rewrite <- not_true_iff_false.
        repeat split.
        + intro Hmem; apply HLength in Hmem; rewrite fill_soundness in Hmem; lia.
        + rewrite iset.mem_spec; rewrite iset.add_spec; auto.
        + intros n H; rewrite iset.mem_spec in H; rewrite iset.add_spec in H; destruct H as [H|].
            - rewrite H; rewrite fill_soundness. lia.
            - rewrite <- iset.mem_spec in H; apply HLength in H; lia.
    }
    case_eq (iset.mem name s); simpl.
    all: intros Hmem HEq.
    {
        apply HRec in HEq; trivial.
    }
    {
        generalize Hmem; clear Hmem.
        inversion HEq; repeat split; auto.
        + rewrite iset.mem_spec; rewrite iset.add_spec; auto.
        + intro; rewrite iset.mem_spec; rewrite iset.add_spec.
            intro H; destruct H as [H|H].
            - destruct H; lia.
            - rewrite <-iset.mem_spec in H; apply HLength in H; lia.
    }
Qed.
