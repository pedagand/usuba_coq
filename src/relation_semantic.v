Require Import List Bool.
Require Import ZArith.
Require Import Coq.Sets.Ensembles.
From mathcomp Require Import seq ssrnat.

From Usuba Require Import ident usuba_AST arch semantic_base list_relations.

Definition lift_value (v : @cst_or_int Z) : @cst_or_int (option Z) :=
    match v with
    | CoIL l => CoIL l
    | CoIR d val form => CoIR d (map Some val) form
    end.

Inductive find_val {A} (v : ident) : list (ident * A) -> A -> Prop :=
    | FVSame : forall ctxt val, find_val v ((v, val) :: ctxt) val
    | FVRec : forall ctxt val v',
        v <> v' -> find_val v ctxt val ->
        find_val v ((v', val) :: ctxt) val.

Inductive eval_arith_expr_inner (ctxt : list (ident * @cst_or_int Z))
    : arith_expr -> Z -> Prop :=
    | EAEConst : forall i, eval_arith_expr_inner ctxt (Const_e i) i
    | EAEVar : forall var i,
        find_val var ctxt (CoIL i) ->
        eval_arith_expr_inner ctxt (Var_e var) i
    | EAEAdd : forall e1 e2 i1 i2,
        eval_arith_expr_inner ctxt e1 i1 ->
        eval_arith_expr_inner ctxt e2 i2 ->
        eval_arith_expr_inner ctxt (Op_e Add e1 e2) (i1 + i2)%Z 
    | EAEMul : forall e1 e2 i1 i2,
        eval_arith_expr_inner ctxt e1 i1 ->
        eval_arith_expr_inner ctxt e2 i2 ->
        eval_arith_expr_inner ctxt (Op_e Mul e1 e2) (i1 * i2)%Z 
    | EAESub : forall e1 e2 i1 i2,
        eval_arith_expr_inner ctxt e1 i1 ->
        eval_arith_expr_inner ctxt e2 i2 ->
        eval_arith_expr_inner ctxt (Op_e Sub e1 e2) (i1 - i2)%Z 
    | EAEMod : forall e1 e2 i1 i2,
        eval_arith_expr_inner ctxt e1 i1 ->
        eval_arith_expr_inner ctxt e2 i2 ->
        eval_arith_expr_inner ctxt (Op_e Mod e1 e2) (i1 mod i2)%Z 
    | EAEDiv : forall e1 e2 i1 i2,
        eval_arith_expr_inner ctxt e1 i1 ->
        eval_arith_expr_inner ctxt e2 i2 ->
        eval_arith_expr_inner ctxt (Op_e Div e1 e2) (i1 / i2)%Z 
.

Definition eval_arith_expr ctxt ae v :=
    eval_arith_expr_inner ctxt ae (Z.of_nat v).

Inductive eval_monop (d : dir) (f : Z -> Z) : @cst_or_int Z -> @cst_or_int Z -> Prop :=
    | EMonop : forall val_in form,
        eval_monop d f (CoIR d val_in form) (CoIR d (map f val_in) form)
.

Inductive list_map2 {A B C} (f : A -> B -> C) : seq A -> seq B -> seq C -> Prop :=
    | LMnil : list_map2 f nil nil nil
    | LMcons : forall h1 h2 t1 t2 t3,
        list_map2 f t1 t2 t3 ->
        list_map2 f (h1 :: t1) (h2 :: t2) (f h1 h2 :: t3)
.

Inductive eval_binop (d : dir) (f : Z -> Z -> Z) : @cst_or_int Z -> @cst_or_int Z -> @cst_or_int Z -> Prop :=
    | EBinop : forall val1 val2 val3 form1 form2,
        list_map2 f val1 val2 val3 ->
        eval_binop d f (CoIR d val1 form1) (CoIR d val2 form2) (CoIR d val3 (scm form1 form2))
.

Inductive is_of_form {A} : nat -> nat -> list (list A) -> Prop :=
    | IoFnil : forall len, is_of_form 0 len nil
    | IoFcons : forall len1 len2 hd tl,
        length hd = len2 ->
        is_of_form len1 len2 tl ->
        is_of_form len1.+1 len2 (hd :: tl)
.

Inductive index_val (ctxt : list (ident * @cst_or_int Z))
    : list nat -> list Z -> list indexing -> list nat -> list Z -> Prop :=
    | IVnil : forall form v, index_val ctxt form v nil form v
    | IVcons_Ind : forall ae i ind dim_hd form1 vL v1 form2 v2,
        eval_arith_expr ctxt ae i ->
        nth_error vL i = Some v1 ->
        is_of_form dim_hd (prod_list form1) vL ->
        index_val ctxt form1 v1 ind form2 v2 ->
        index_val ctxt (dim_hd :: form1) (flatten vL) (IInd ae :: ind) form2 v2
    | IVcons_Slice : forall aeL iL ind dim_hd form1 vL_in vL_split form2 vL_out,
        list_rel (eval_arith_expr ctxt) aeL iL ->
        list_rel (fun i v => nth_error vL_in i = Some v) iL vL_split ->
        is_of_form dim_hd (prod_list form1) vL_in ->
        list_rel (fun v1 v2 => index_val ctxt form1 v1 ind form2 v2) vL_split vL_out ->
        index_val ctxt (dim_hd :: form1) (flatten vL_in) (ISlice aeL :: ind) form2 (flatten vL_out)
    | IVcons_Range : forall ae1 ae2 i1 i2 ind dim_hd form1 vL_in vL_split form2 vL_out,
        eval_arith_expr ctxt ae1 i1 -> eval_arith_expr ctxt ae2 i2 ->
        list_rel (fun i v => nth_error vL_in i = Some v) (gen_range i1 i2) vL_split ->
        is_of_form dim_hd (prod_list form1) vL_in ->
        list_rel (fun v1 v2 => index_val ctxt form1 v1 ind form2 v2) vL_split vL_out ->
        index_val ctxt (dim_hd :: form1) (flatten vL_in) (IRange ae1 ae2 :: ind) form2 (flatten vL_out)
.

Inductive eval_var (ctxt : list (ident * @cst_or_int Z)) : var -> @cst_or_int Z -> Prop :=
    | EVVar : forall v val,
        find_val v ctxt val -> eval_var ctxt (Var v) val
    | EVIndex : forall v d form1 form2 val1 val2 ind,
        eval_var ctxt v (CoIR d val1 form1) ->
        index_val ctxt form1 val1 ind form2 val2 ->
        eval_var ctxt (Index v ind) (CoIR d val2 form2)
.

Inductive eval_bvar_to (ctxt : list (ident * @cst_or_int Z))
    : bvar -> cst_or_int -> Prop :=
    | EBTCoIR : forall v ind dir form1 val1 form2 val2,
        find_val v ctxt (CoIR dir val1 form1) ->
        index_val ctxt form1 val1 ind form2 val2 ->
        eval_bvar_to ctxt (v, ind) (CoIR dir val2 form2)
    | EBTCoIL : forall v val,
        find_val v ctxt (CoIL val) ->
        eval_bvar_to ctxt (v, nil) (CoIL val)
.

Inductive eval_bvars_to (ctxt : list (ident * @cst_or_int Z))
    : seq bvar -> seq (@cst_or_int Z) -> Prop :=
    | EBsTnil : eval_bvars_to ctxt nil nil 
    | EBsCons : forall hd tl v_hd v_tl,
        eval_bvar_to ctxt hd v_hd ->
        eval_bvars_to ctxt tl v_tl ->
        eval_bvars_to ctxt (hd :: tl) (v_hd :: v_tl)
.

Inductive eval_expr_to (arch : architecture)
    : prog -> list (ident * @cst_or_int Z) -> expr -> list (@cst_or_int Z) -> Prop :=
    | EETConstN1 : forall fprog ctxt n,
        eval_expr_to arch fprog ctxt (Const n None) [:: CoIL n]
    | EETConstN2 : forall fprog ctxt n typ v,
        build_integer typ n = Some v ->
        eval_expr_to arch fprog ctxt (Const n None) v
    | EETConstS : forall fprog ctxt n typ v,
        build_integer typ n = Some v ->
        eval_expr_to arch fprog ctxt (Const n (Some typ)) v
    | EETVar : forall fprog ctxt var v,
        eval_var ctxt var v ->
        eval_expr_to arch fprog ctxt (ExpVar var) [:: v]
    | EETBuildA : forall fprog ctxt el len values form d,
        eval_expr_list_to' arch fprog ctxt el len values form d ->
        eval_expr_to arch fprog ctxt (BuildArray el) [:: CoIR d values (len :: form)]
    | EETTuple : forall fprog ctxt el values,
        eval_expr_list_to arch fprog ctxt el values ->
        eval_expr_to arch fprog ctxt (BuildArray el) values
    | EETNot : forall fprog ctxt dir e val val' f,
        eval_expr_to arch fprog ctxt e [:: val] ->
        arith_wrapper (IMPL_LOG arch) lnot dir = Some f ->
        eval_monop dir f val val' ->
        eval_expr_to arch fprog ctxt (Not e) [:: val']
    | EETLog : forall fprog ctxt d op e1 e2 val1 val2 f val_out,
        eval_expr_to arch fprog ctxt e1 [:: val1] ->
        eval_expr_to arch fprog ctxt e2 [:: val2] ->
        match op with
            | And | Masked And => arith_wrapper (IMPL_LOG arch) land d
            | Or | Masked Or =>   arith_wrapper (IMPL_LOG arch) lor d
            | Xor | Masked Xor =>   arith_wrapper (IMPL_LOG arch) lxor d
            | Andn | Masked Andn => arith_wrapper (IMPL_LOG arch) landn d
            | Masked (Masked _) => None
        end = Some f ->
        eval_binop d f val1 val2 val_out ->
        eval_expr_to arch fprog ctxt (Log op e1 e2) [:: val_out]
    | EETArith : forall fprog ctxt dir f op e1 e2 val1 val2 val_out,
        eval_expr_to arch fprog ctxt e1 [:: val1] ->
        eval_expr_to arch fprog ctxt e2 [:: val2] ->
        match op with
            | Add => arith_wrapper (IMPL_ARITH arch) add_fun dir
            | Sub => arith_wrapper (IMPL_ARITH arch) sub_fun dir
            | Div => arith_wrapper (IMPL_ARITH arch) div_fun dir
            | Mod => arith_wrapper (IMPL_ARITH arch) mod_fun dir
            | Mul => arith_wrapper (IMPL_ARITH arch) mul_fun dir
        end = Some f ->
        eval_binop dir f val1 val2 val_out ->
        eval_expr_to arch fprog ctxt (Arith op e1 e2) [:: val_out]
    | EETShift : forall fprog ctxt op e ae val i val_out,
        eval_expr_to arch fprog ctxt e val ->
        eval_arith_expr ctxt ae i ->
        eval_shift arch op val i = Some val_out ->
        eval_expr_to arch fprog ctxt (Shift op e ae) val_out
    (* TODO : Shuffle Bitmask Pack *)
    (* TODO coercion *)
    | EETFun : forall fprog ctxt v el val_args val_out,
        eval_expr_list_to arch fprog ctxt el val_args ->
        eval_prog_to arch fprog v val_args None val_out ->
        eval_expr_to arch fprog ctxt (Fun v el) val_out
    | EETFun_v : forall fprog ctxt v ae i el val_args val_out,
        eval_expr_list_to arch fprog ctxt el val_args ->
        eval_arith_expr ctxt ae i ->
        eval_prog_to arch fprog v val_args (Some i) val_out ->
        eval_expr_to arch fprog ctxt (Fun_v v ae el) val_out
with eval_expr_list_to' (arch : architecture)
    : prog -> list (ident * @cst_or_int Z) -> expr_list -> nat -> list Z -> list nat -> dir -> Prop :=
    | EETLnil' : forall fprog ctxt form d,
        eval_expr_list_to' arch fprog ctxt Enil 0 nil form d
    | EETcons'_CoIL : forall fprog ctxt hd tl dir v len l_tl,
        eval_expr_to arch fprog ctxt hd [:: CoIL v] ->
        eval_expr_list_to' arch fprog ctxt tl len l_tl nil dir ->
        eval_expr_list_to' arch fprog ctxt (ECons hd tl) len.+1 (v :: l_tl) nil dir
    | EETcons'_CoIR : forall fprog ctxt hd tl dir l_hd form len l_tl,
        eval_expr_to arch fprog ctxt hd [:: CoIR dir l_hd form] ->
        eval_expr_list_to' arch fprog ctxt tl len l_tl form dir ->
        eval_expr_list_to' arch fprog ctxt (ECons hd tl) len.+1 (l_hd ++ l_tl) form dir
with eval_expr_list_to (arch : architecture) 
    : prog -> list (ident * @cst_or_int Z) -> expr_list -> list (@cst_or_int Z) -> Prop :=
    | EETLnil : forall fprog ctxt, eval_expr_list_to arch fprog ctxt Enil nil
    | EETLcons : forall fprog ctxt hd tl val_hd val_tl,
        eval_expr_to arch fprog ctxt hd val_hd ->
        eval_expr_list_to arch fprog ctxt tl val_tl ->
        eval_expr_list_to arch fprog ctxt (ECons hd tl) (val_hd ++ val_tl)
with check_deq (arch : architecture)
    : prog -> list (ident * @cst_or_int Z) -> deq -> Prop :=
    | CDEqn : forall fprog ctxt (vars : seq bvar) e val,
        eval_expr_to arch fprog ctxt e val ->
        eval_bvars_to ctxt vars val ->
        check_deq arch fprog ctxt (Eqn vars e false)
    | CDLoop : forall fprog ctxt i start_e start_i end_e end_i deqs opt,
        eval_arith_expr ctxt start_e start_i ->
        eval_arith_expr ctxt end_e end_i ->
        (forall ind,
            start_i <= ind = true ->
            ind <= end_i = true ->
            check_deq_list arch fprog ((i, CoIL (Z.of_nat ind)) :: ctxt) deqs) ->
        check_deq arch fprog ctxt (Loop i start_e end_e deqs opt)
with check_deq_list (arch : architecture)
    : prog -> list (ident * @cst_or_int Z) -> list_deq -> Prop :=
    | CDLnil : forall fprog ctxt, check_deq_list arch fprog ctxt Dnil
    | CDLcons : forall fprog ctxt deq_hd deq_tl,
        check_deq arch fprog ctxt deq_hd ->
        check_deq_list arch fprog ctxt deq_tl ->
        check_deq_list arch fprog ctxt (Dcons deq_hd deq_tl)
with eval_node_to (arch : architecture)
    : prog -> p -> p -> def_i -> option nat -> list (@cst_or_int Z) -> list (@cst_or_int Z) -> Prop :=
    | EVTSingle :
        forall fprog in_names temp_names out_names in_values out_values eqns ctxt,
        eval_bvars_to ctxt (map (fun v => (VD_ID v, nil)) in_names) in_values ->
        eval_bvars_to ctxt (map (fun v => (VD_ID v, nil)) out_names) out_values ->
        check_deq_list arch fprog ctxt eqns ->
        eval_node_to arch fprog in_names out_names (Single temp_names eqns) None in_values out_values
    | EVTMultiple :
        forall fprog in_names out_names nodes ind in_values out_values,
            eval_node_list_to arch fprog in_names out_names nodes ind in_values out_values ->
            eval_node_to arch fprog in_names out_names (Multiple nodes) (Some ind) in_values out_values
with eval_node_list_to (arch : architecture)
    : prog -> p -> p -> list_def_i -> nat -> list (@cst_or_int Z) -> list (@cst_or_int Z) -> Prop :=
    | ENLBase : forall fprog in_names out_names node nodes in_values out_values,
        eval_node_to arch fprog in_names out_names node None in_values out_values ->
        eval_node_list_to arch fprog in_names out_names (LDcons node nodes) 0 in_values out_values
    | ENLSucc : forall fprog in_names out_names node nodes ind in_values out_values,
        eval_node_list_to arch fprog in_names out_names nodes ind in_values out_values ->
        eval_node_list_to arch fprog in_names out_names (LDcons node nodes) ind.+1 in_values out_values
with eval_prog_to (arch : architecture)
    : prog -> ident -> list (@cst_or_int Z) -> option nat -> list (@cst_or_int Z) -> Prop :=
    | EPTSame : forall fprog in_values opt out_values node infered,
        infer_types (P_IN node) in_values = Some infered ->
        eval_node_to arch fprog (subst_infer_p infered (P_IN node))
            (subst_infer_p infered (P_OUT node)) (subst_infer_def infered (NODE node)) opt in_values out_values ->
        eval_prog_to arch (node :: fprog) (ID node) in_values opt out_values
    | EPTDiff : forall fprog v node in_values opt out_values,
        v <> ID node ->
        eval_prog_to arch fprog v in_values opt out_values ->
        eval_prog_to arch (node :: fprog) v in_values opt out_values
.
