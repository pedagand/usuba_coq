Require Import usuba_AST.
Require Import String.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
From mathcomp Require Import all_ssreflect.
Require Setoid.
Check internal_log_op_dec_bl.

Lemma empty_ctxt_alpha_eq_ident:
    forall id1 id2,
        alpha_equal_ident (NatMap.empty ident) id1 id2 <-> id1 = id2.
Proof.
    unfold alpha_equal_ident.
    move=> id1 id2; split; move=> H.
        by apply: internal_string_dec_bl.
        by apply: internal_string_dec_lb.
Qed.

Lemma empty_ctxt_alpha_equal_arith_expr:
    forall e1 e2,
    alpha_equal_arith_expr (NatMap.empty ident) e1 e2 <-> e1 = e2.
Proof.
    move => e1.
    induction e1 as [n1 | id1 | aop e1_1 RecH1 e1_2 RecH2]; simpl.
    { move => [n2 | id2 | ]; split=> H.
        + pose H2 := PeanoNat.Nat.eqb_eq n1 n2.
          destruct H2 as [H3 H4].
          auto.
        + pose H2 := PeanoNat.Nat.eqb_eq n1 n2.
          destruct H2 as [H3 H4].
          apply:H4.
          injection H.
          auto.
        + discriminate.
        + discriminate.
        + discriminate.
        + discriminate.
    }
    {
        move => [n2 | id2 | ]; split=> H.
        + discriminate.
        + discriminate.
        + move/empty_ctxt_alpha_eq_ident : H.
            move=> ->.
            reflexivity.
        + injection H.
            move=> ->.
            pose H2 := empty_ctxt_alpha_eq_ident id2 id2.
            destruct H2 as [H0 H1].
            apply: H1. reflexivity.
        + discriminate.
        + discriminate.
    }
    {
        move=> [n2 | id2 | op e2_1 e2_2]; split.
        + discriminate.
        + discriminate.
        + discriminate.
        + discriminate.
        + move/andP => [H0 H1]; move: H0.
            move/andP => [H2 H3].
            specialize RecH1 with e2_1.
            specialize RecH2 with e2_2.
            setoid_rewrite RecH1 in H3.
            setoid_rewrite RecH2 in H1.
            pose Heq := internal_arith_op_dec_bl aop op H2.
            rewrite Heq H1 H3.
            by [].
        + move => [H0 H1 H2].
            specialize RecH1 with e2_1.
            specialize RecH2 with e2_2.
            destruct RecH1 as [_ RecH12].
            pose RecH12b := RecH12 H1.
            destruct RecH2 as [_ RecH22].
            pose RecH22b := RecH22 H2.
            rewrite RecH12b RecH22b.
            rewrite andbT.
            rewrite andbT.
            apply: internal_arith_op_dec_lb.
            assumption.
    }
Qed.
