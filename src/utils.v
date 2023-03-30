From mathcomp Require Import all_ssreflect.

Ltac impl_tac :=
    lazymatch goal with
    | |- (?A -> ?B) -> ?C =>
        let H := fresh "H" in
        let H2 := fresh "H" in
        let H3 := fresh "H" in
        assert A as H; [> idtac | (move=> H2; pose (H3 := H2 H); move: H3; clear H2 H)]
    end.

Ltac eq_match :=
    lazymatch goal with
    | |- match ?A with Some _ => _ | None => _ end = match ?B with Some _ => _ | None => _  end =>
        let H := fresh "H" in
        assert (A = B) as H; [> idtac | rewrite H; reflexivity]
    end.

Ltac small_eq_match :=
    lazymatch goal with
    | |- match ?A with Some _ => _ | None => _ end = match ?B with Some _ => _ | None => _  end =>
        let H := fresh "H" in
        assert (A = B) as H; [> idtac | rewrite H; destruct B]
    end.
