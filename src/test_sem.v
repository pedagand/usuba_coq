From mathcomp Require Import all_ssreflect.
From Usuba Require Import usuba_AST usuba_sem.

Lemma eval_asign:
    forall arch prog ctxt opt_ctxt' value1 var,
        find_val ctxt var = Some (ValTuple (lV_cons value1 lV_nil)) ->
        eval_deq arch prog ctxt
            (Eqn (VTuple (LVcons (Index (Var var) (Const_e 0)) (LVcons (Index (Var var) (Const_e 0)) LVnil))) (Tuple (ECons (Const 1 None)
                            (ECons (Const 2 None) Enil)))
                true) = opt_ctxt'
        -> (ctxt' <- opt_ctxt'; find_val ctxt' var) = Some (ValTuple (lV_cons (VConst 2) lV_nil)).
Proof.
    simpl.
    move=> _ _ ctxt opt_ctxt val var ->; simpl.
    rewrite String.eqb_refl.
    move=> <-; simpl.
    rewrite String.eqb_refl; reflexivity.
Qed.
