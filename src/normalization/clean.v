From Usuba Require Import ident usuba_AST collect.
From Coq Require Import Bool.Bool.

Function clean_in_deqs (vars : iset.t) (dL : list_deq) : iset.t * list_deq :=
    match dL with
    | Dcons (Eqn v e l) tl =>
        let (vars', tl) := clean_in_deqs vars tl in 
        let bound_vars := collect_varl v in
        if iset.exists_ (fun i => iset.mem i vars') bound_vars
        then (iset.union vars' (iset.union (collect_varl v) (collect_expr e)), Dcons (Eqn v e l) tl)
        else (vars', tl)
    | Dcons (Loop i ae1 ae2 body opt) tl =>
        let (vars', tl') := clean_in_deqs vars tl in
        let bounds := collect_bounddeqs body in
        if iset.exists_ (fun elt => iset.mem elt vars') bounds || iset.mem i vars'
        then (iset.add i (iset.union vars' (iset.union (iset.union (collect_aexpr ae1) (collect_aexpr ae2)) (collect_deqs body))), Dcons (Loop i ae1 ae2 body opt) tl')
        else (vars', tl')
    | Dnil => (vars, Dnil)
    end.

Definition clean_node (node : def) : def :=
    match NODE node with
    | Single p eqns =>
        {|
            NODE := Single p (snd (clean_in_deqs (collect_vdecl (P_OUT node)) eqns));
            ID := ID node;
            P_IN := P_IN node;
            P_OUT := P_OUT node;
            OPT := OPT node
        |}
    | _ => node
    end.

Definition clean_prog : prog -> prog := List.map clean_node.
