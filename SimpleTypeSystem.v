Section SimpleTypeSystem.
Require Import PatternMatching.
Require Import ZArith.
Open Scope Z_scope.

(* Types at p.125 *)
Inductive Types : Set :=
    | TBool : Types
    | TInt  : Types
    | TFun  : Types -> Types -> Types
    | TList : Types -> Types.

(* Type environments at p.125 *)
Inductive TEnv : Set :=
    | TEEmpty : TEnv
    | TEBind  : TEnv -> Var -> Types -> TEnv.

(* Type lookup at p.124 *)
Inductive has_type : TEnv -> Var -> Types -> Prop :=
    | HT_Bind1 : forall (C : TEnv) (x : Var) (t : Types),
                 has_type (TEBind C x t) x t
    | HT_Bind2 : forall (C : TEnv) (x y : Var) (t t0 : Types),
                 has_type C x t -> y <> x ->
                 has_type (TEBind C y t0) x t.

(* Fig 8.1 and 8.2 *)
Inductive Typable : TEnv -> Exp -> Types -> Prop :=
    | T_Int    : forall (C : TEnv) (i : Z),
                 Typable C (EInt i) TInt
    | T_Bool   : forall (C : TEnv) (b : bool),
                 Typable C (EBool b) TBool
    | T_If     : forall (C : TEnv) (e1 e2 e3 : Exp) (t : Types),
                 Typable C e1 TBool -> Typable C e2 t -> Typable C e3 t ->
                 Typable C (EIf e1 e2 e3) t
    | T_Plus   : forall (C : TEnv) (e1 e2 : Exp),
                 Typable C e1 TInt -> Typable C e2 TInt ->
                 Typable C (EPlus e1 e2) TInt
    | T_Minus  : forall (C : TEnv) (e1 e2 : Exp),
                 Typable C e1 TInt -> Typable C e2 TInt ->
                 Typable C (EMinus e1 e2) TInt
    | T_Times  : forall (C : TEnv) (e1 e2 : Exp),
                 Typable C e1 TInt -> Typable C e2 TInt ->
                 Typable C (ETimes e1 e2) TInt
    | T_Lt     : forall (C : TEnv) (e1 e2 : Exp),
                 Typable C e1 TInt -> Typable C e2 TInt ->
                 Typable C (ELt e1 e2) TBool
    | T_Var    : forall (C : TEnv) (x : Var) (t : Types),
                 has_type C x t ->
                 Typable C (EVar x) t
    | T_Let    : forall (C : TEnv) (e1 e2 : Exp) (x : Var) (t1 t2 : Types),
                 Typable C e1 t1 -> Typable (TEBind C x t1) e2 t2 ->
                 Typable C (ELet x e1 e2) t2
    | T_Fun    : forall (C : TEnv) (e : Exp) (x : Var) (t1 t2 : Types),
                 Typable (TEBind C x t1) e t2 ->
                 Typable C (EFun x e) (TFun t1 t2)
    | T_App    : forall (C : TEnv) (e1 e2 : Exp) (t1 t2 : Types),
                 Typable C e1 (TFun t1 t2) -> Typable C e2 t1 ->
                 Typable C (EApp e1 e2) t2
    | T_LetRec : forall (C : TEnv) (e1 e2 : Exp) (x y : Var) (t t1 t2 : Types),
                 Typable (TEBind (TEBind C x (TFun t1 t2)) y t1) e1 t2 ->
                 Typable (TEBind C x (TFun t1 t2)) e2 t ->
                 Typable C (ELetRec x y e1 e2) t
    | T_Nil    : forall (C : TEnv) (t : Types),
                 Typable C ENil (TList t)
    | T_Cons   : forall (C : TEnv) (e1 e2 : Exp) (t : Types),
                 Typable C e1 t -> Typable C e2 (TList t) ->
                 Typable C (ECons e1 e2) (TList t)
    | T_Match  : forall (C : TEnv) (e1 e2 e3 : Exp) (x y : Var) (t t' : Types),
                 Typable C e1 (TList t') -> Typable C e2 t ->
                 Typable (TEBind (TEBind C x t') y (TList t')) e3 t ->
                 Typable C (EMatch e1 e2 x y e3) t.

(* Domains (reuesed) *)
Inductive in_dom : Env -> Var -> Prop :=
    | Dom_EBind1 : forall (E : Env) (x : Var) (v : Value),
                   in_dom (EBind E x v) x
    | Dom_EBind2 : forall (E : Env) (x y : Var) (v : Value),
                   in_dom E x -> in_dom (EBind E y v) x.

(* Fig 8.3, 8.4 and 8.5 *)
Inductive Error : Env -> Exp -> Prop :=
    | E_IfErr1  : forall (E : Env) (e1 e2 e3 : Exp),
                    not_bool E e1 ->
                    Error E (EIf e1 e2 e3)
    | E_IfErr2    : forall (E : Env) (e1 e2 e3 : Exp),
                    EvalTo E e1 (VBool true) -> Error E e2 ->
                    Error E (EIf e1 e2 e3)
    | E_IfErr3    : forall (E : Env) (e1 e2 e3 : Exp),
                    EvalTo E e1 (VBool false) -> Error E e3 ->
                    Error E (EIf e1 e2 e3)
    | E_PlusErr1  : forall (E : Env) (e1 e2 : Exp),
                    not_int E e1 ->
                    Error E (EPlus e1 e2)
    | E_PlusErr2  : forall (E : Env) (e1 e2 : Exp) (i1 : Z),
                    EvalTo E e1 (VInt i1) -> not_int E e2 ->
                    Error E (EPlus e1 e2)
    | E_MinusErr1 : forall (E : Env) (e1 e2 : Exp),
                    not_int E e1 ->
                    Error E (EMinus e1 e2)
    | E_MinusErr2 : forall (E : Env) (e1 e2 : Exp) (i1 : Z),
                    EvalTo E e1 (VInt i1) -> not_int E e2 ->
                    Error E (EMinus e1 e2)
    | E_TimesErr1 : forall (E : Env) (e1 e2 : Exp),
                    not_int E e1 ->
                    Error E (ETimes e1 e2)
    | E_TimesErr2 : forall (E : Env) (e1 e2 : Exp) (i1 : Z),
                    EvalTo E e1 (VInt i1) -> not_int E e2 ->
                    Error E (ETimes e1 e2)
    | E_LtErr1    : forall (E : Env) (e1 e2 : Exp),
                    not_int E e1 ->
                    Error E (ELt e1 e2)
    | E_LtErr2    : forall (E : Env) (e1 e2 : Exp) (i1 : Z),
                    EvalTo E e1 (VInt i1) -> not_int E e2 ->
                    Error E (ELt e1 e2)
    | E_VarErr    : forall (E : Env) (x : Var),
                    ~ in_dom E x ->
                    Error E (EVar x)
    | E_LetErr1   : forall (E : Env) (e1 e2 : Exp) (x : Var),
                    Error E e1 ->
                    Error E (ELet x e1 e2)
    | E_LetErr2   : forall (E : Env) (e1 e2 : Exp) (x : Var) (v1 : Value),
                    EvalTo E e1 v1 -> Error (EBind E x v1) e2 ->
                    Error E (ELet x e1 e2)
    | E_AppErr1   : forall (E : Env) (e1 e2 : Exp),
                    not_closure E e1 ->
                    Error E (EApp e1 e2)
    | E_AppErr2   : forall (E E2 : Env) (e1 e2 e0 : Exp) (x : Var),
                    EvalTo E e1 (VFun E2 x e0) -> Error E e2 ->
                    Error E (EApp e1 e2)
    | E_AppErr3   : forall (E E2 : Env) (e1 e2 e0 : Exp) (x y : Var),
                    EvalTo E e1 (VRecFun E2 x y e0) -> Error E e2 ->
                    Error E (EApp e1 e2)
    | E_AppErr4   : forall (E E2 : Env) (e1 e2 e0 : Exp) (x : Var) (v2 : Value),
                    EvalTo E e1 (VFun E2 x e0) -> EvalTo E e2 v2 ->
                    Error (EBind E x v2) e0 ->
                    Error E (EApp e1 e2)
    | E_AppErr5   : forall (E E2 : Env) (e1 e2 e0 : Exp)
                           (x y : Var) (v2 : Value),
                    EvalTo E e1 (VRecFun E2 x y e0) -> EvalTo E e2 v2 ->
                    Error (EBind (EBind E x (VRecFun E2 x y e0)) y v2) e0 ->
                    Error E (EApp e1 e2)
    | E_LetRecErr : forall (E : Env) (e1 e2 : Exp) (x y : Var),
                    Error (EBind E x (VRecFun E x y e1)) e2 ->
                    Error E (ELetRec x y e1 e2)
    | E_ConsErr1  : forall (E : Env) (e1 e2 : Exp),
                    Error E e1 ->
                    Error E (ECons e1 e2)
    | E_ConsErr2  : forall (E : Env) (e1 e2 : Exp) (v1 : Value),
                    EvalTo E e1 v1 -> Error E e2 ->
                    Error E (ECons e1 e2)
    | E_MatchErr1 : forall (E : Env) (e1 e2 e3 : Exp) (x y : Var),
                    not_list E e1 ->
                    Error E (EMatch e1 e2 x y e3)
    | E_MatchErr2 : forall (E : Env) (e1 e2 e3 : Exp) (x y : Var),
                    EvalTo E e1 VNil -> Error E e2 ->
                    Error E (EMatch e1 e2 x y e3)
    | E_MatchErr3 : forall (E : Env) (e1 e2 e3 : Exp)
                           (x y : Var) (v1 v2 : Value),
                    EvalTo E e1 (VCons v1 v2) ->
                    Error (EBind (EBind E x v1) y v2) e3 ->
                    Error E (EMatch e1 e2 x y e3)
    with not_int : Env -> Exp -> Prop :=
    | NI_Value : forall (E : Env) (e : Exp) (v : Value),
                 EvalTo E e v -> (forall i : Z, v <> VInt i) ->
                 not_int E e
    | NI_Error : forall (E : Env) (e : Exp),
                 Error E e ->
                 not_int E e
    with not_bool : Env -> Exp -> Prop :=
    | NB_Value : forall (E : Env) (e : Exp) (v : Value),
                 EvalTo E e v -> (forall b : bool, v <> VBool b) ->
                 not_bool E e
    | NB_Error : forall (E : Env) (e : Exp),
                 Error E e ->
                 not_bool E e
    with not_closure : Env -> Exp -> Prop :=
    | NC_Value : forall (E : Env) (e : Exp) (v : Value),
                 EvalTo E e v ->
                 (forall (E0 : Env) (x0 : Var) (e0 : Exp), v <> VFun E0 x0 e0) ->
                 (forall (E0 : Env) (x0 y0 : Var) (e0 : Exp),
                  v <> VRecFun E0 x0 y0 e0) ->
                 not_closure E e
    | NC_Error : forall (E : Env) (e : Exp),
                 Error E e ->
                 not_closure E e
    with not_list : Env -> Exp -> Prop :=
    | NL_Value : forall (E : Env) (e : Exp) (v : Value),
                 EvalTo E e v -> v <> VNil ->
                 (forall v1 v2 : Value, v <> VCons v1 v2) ->
                 not_list E e
    | NL_Error : forall (E : Env) (e : Exp),
                 Error E e ->
                 not_list E e.

(* Fig 8.6 *)
Inductive ValueCompat : Value -> Types -> Prop :=
    | VC_Int    : forall i : Z, ValueCompat (VInt i) TInt
    | VC_Bool   : forall b : bool, ValueCompat (VBool b) TBool
    | VC_Fun    : forall (E : Env) (C : TEnv) (e : Exp)
                         (x : Var) (t1 t2 : Types),
                  EnvCompat E C -> Typable (TEBind C x t1) e t2 ->
                  ValueCompat (VFun E x e) (TFun t1 t2)
    | VC_RecFun : forall (E : Env) (C : TEnv) (e : Exp)
                         (x y : Var) (t1 t2 : Types),
                  EnvCompat E C -> Typable (TEBind (TEBind C x t1) y t1) e t2 ->
                  ValueCompat (VRecFun E x y e) (TFun t1 t2)
    | VC_Nil    : forall t' : Types, ValueCompat VNil (TList t')
    | VC_Cons   : forall (t' : Types) (v1 v2 : Value),
                  ValueCompat v1 t' -> ValueCompat v2 (TList t') ->
                  ValueCompat (VCons v1 v2) (TList t')
    with EnvCompat : Env -> TEnv -> Prop :=
    | EC_Empty : EnvCompat EEmpty TEEmpty
    | EC_Bind  : forall (E' : Env) (C' : TEnv)
                        (x : Var) (v : Value) (t : Types),
                 EnvCompat E' C' -> ValueCompat v t ->
                 EnvCompat (EBind E' x v) (TEBind C' x t).

(* Uniqueness of the evaluation *)
Lemma EvalTo_uniq :
    forall (E : Env) (e : Exp) (v v' : Value),
    EvalTo E e v -> EvalTo E e v' -> v = v'.
Proof.
Admitted.

(* Type preservation *)
Lemma type_safety_preserve :
    forall (E : Env) (C : TEnv) (e : Exp) (t : Types) (v : Value),
    Typable C e t -> EvalTo E e v -> EnvCompat E C ->
    ValueCompat v t.
Proof.
Admitted.

(* Progress *)
Lemma type_safety_progres :
    forall (E : Env) (C : TEnv) (e : Exp) (t : Types) (v : Value),
    Typable C e t -> EnvCompat E C -> ~ Error E e.
Proof.
Admitted.

Inductive halt : Env -> Exp -> Prop :=
    | H_Value : forall (E : Env) (e : Exp) (v : Value),
                EvalTo E e v -> halt E e
    | H_Error : forall (E : Env) (e : Exp),
                Error E e -> halt E e.

(* Theorem 8.3 *)
Theorem type_safety_general :
    forall (E : Env) (C : TEnv) (e : Exp) (t : Types),
    Typable C e t -> halt E e -> EnvCompat E C ->
    (exists v : Value, EvalTo E e v /\ ValueCompat v t).
Proof.
    intros E C e t Ht Hh.
    generalize dependent t.
    generalize dependent C.
    inversion Hh; subst.

        (* Case : Hh is from H_Value *)
        induction H as [ E i | E b | E x v Hv |
                         E e1 e2 i1 i2 i3 He1 He1' He2 He2' Hp |
                         E e1 e2 i1 i2 i3 He1 He1' He2 He2' Hm |
                         E e1 e2 i1 i2 i3 He1 He1' He2 He2' Htm |
                         E e1 e2 i1 i2 b3 He1 He1' He2 He2' Hl |
                         E e1 e2 e3 v He1 He1' He2 He2' |
                         E e1 e2 e3 v He1 He1' He3 He3' |
                         E e1 e2 x v' v He1 He1' He2 He2' | E x e |
                         E E2 e1 e2 e0 x v v2 He1 He1' He2 He2' He0 He0' |
                         | | E | E e1 e2 v1 v2 He1 He1' He2 He2' |
                         E e1 e2 e3 v x y He1 He1' He2 He2' |
                         E e1 e2 e3 x y v v1 v2 He1 He1' He3 He3' ].

            (* Case : H is from E_Int *)
            intros C t Ht HC.
            exists (VInt i).
            inversion Ht; subst.
            apply (conj (E_Int _ _) (VC_Int _)).

            (* Case : H is from E_Bool *)
            intros C t Ht HC.
            exists (VBool b).
            inversion Ht; subst.
            apply (conj (E_Bool _ _) (VC_Bool _)).

            (* Case : H is from E_Var *)
            admit.

            (* Case : H is from E_Plus *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VInt i3).
            apply (conj (E_Plus _ _ _ _ _ _ He1 He2 Hp) (VC_Int _)).

            (* Case : H is from E_Minus *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VInt i3).
            apply (conj (E_Minus _ _ _ _ _ _ He1 He2 Hm) (VC_Int _)).

            (* Case : H is from E_Times *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VInt i3).
            apply (conj (E_Times _ _ _ _ _ _ He1 He2 Htm) (VC_Int _)).

            (* Case : H is from E_Lt *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VBool b3).
            apply (conj (E_Lt _ _ _ _ _ _ He1 He2 Hl) (VC_Bool _)).

            (* Case : H is from E_IfT *)
            intros C t Ht HC.
            inversion Ht; subst.
            specialize (He2' (H_Value _ _ _ He2) _ _ H5 HC).
            destruct He2' as [v2 [Hv2 He2']].
            assert (v = v2) by apply (EvalTo_uniq _ _ _ _ He2 Hv2); subst.
            exists v2.
            apply (conj (E_IfT _ _ _ _ _ He1 He2) He2').

            (* Case : H is from E_IfF *)
            intros C t Ht HC.
            inversion Ht; subst.
            specialize (He3' (H_Value _ _ _ He3) _ _ H6 HC).
            destruct He3' as [v3 [Hv3 He3']].
            assert (v = v3) by apply (EvalTo_uniq _ _ _ _ He3 Hv3); subst.
            exists v3.
            apply (conj (E_IfF _ _ _ _ _ He1 He3) He3').

            (* Case : H is from E_Let *)
            intros C t Ht HC.
            inversion Ht; subst.
            specialize (He1' (H_Value _ _ _ He1) _ _ H4 HC).
            destruct He1' as [v1 [Hv1 He1']].
            assert (v' = v1) by apply (EvalTo_uniq _ _ _ _ He1 Hv1); subst.
            specialize (He2' (H_Value _ _ _ He2) _ _ H5
                             (EC_Bind _ _ _ _ _ HC He1')).
            destruct He2' as [v2 [Hv2 He2']].
            exists v2.
            apply (conj (E_Let _ _ _ _ _ _ Hv1 Hv2) He2').

            (* Case : H is from E_Fun *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VFun E x e).
            apply (conj (E_Fun _ _ _) (VC_Fun _ _ _ _ _ _ HC H3)).

            (* Case : H is from E_App *)
            admit.

            (* Case : H is from E_LetRec *)
            admit.

            (* Case : H is from E_AppRec *)
            admit.

            (* Case : H is from E_Nil *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists VNil.
            apply (conj (E_Nil _) (VC_Nil _)).

            (* Case : H is from E_Cons *)
            intros C t Ht HC.
            inversion Ht; subst.
            specialize (He1' (H_Value _ _ _ He1) _ _ H2 HC).
            destruct He1' as [v1' [Hv1' He1']].
            assert (v1 = v1') by apply (EvalTo_uniq _ _ _ _ He1 Hv1'); subst.
            specialize (He2' (H_Value _ _ _ He2) _ _ H4 HC).
            destruct He2' as [v2' [Hv2' He2']].
            assert (v2 = v2') by apply (EvalTo_uniq _ _ _ _ He2 Hv2'); subst.
            exists (VCons v1' v2').
            apply (conj (E_Cons _ _ _ _ _ Hv1' Hv2') (VC_Cons _ _ _ He1' He2')).

            (* Case : H is from E_MatchNil *)
            intros C t Ht HC.
            inversion Ht; subst.
            specialize (He1' (H_Value _ _ _ He1) _ _ H6 HC).
            destruct He1' as [v1 [Hv1 He1']].
            assert (VNil = v1) by apply (EvalTo_uniq _ _ _ _ He1 Hv1); subst.
            specialize (He2' (H_Value _ _ _ He2) _ _ H7 HC).
            destruct He2' as [v2 [Hv2 He2']].
            assert (v = v2) by apply (EvalTo_uniq _ _ _ _ He2 Hv2); subst.
            exists v2.
            apply (conj (E_MatchNil _ _ _ _ _ _ _ Hv1 Hv2) He2').

            (* Case : H is from E_MatchCons *)
            admit.

        (* Case : Hh is from H_Error *)
        admit.
Qed.

(* Theorem 8.1 *)
Theorem type_safety :
    forall (e : Exp) (t t1 t2 t' : Types) (v : Value),
    Typable TEEmpty e t -> halt EEmpty e ->
    (t = TInt ->
     exists i : Z, EvalTo EEmpty e (VInt i)) /\
    (t = TBool ->
     exists b : bool, EvalTo EEmpty e (VBool b)) /\
    (t = TFun t1 t2 ->
     exists (E : Env) (x : Var) (e : Exp),
         EvalTo EEmpty e (VFun E x e) \/
     exists (E : Env) (x y : Var) (e : Exp),
         EvalTo EEmpty e (VRecFun E x y e)) /\
    (t = TList t' ->
     EvalTo EEmpty e VNil \/
     exists v1 v2 : Value, EvalTo EEmpty e (VCons v1 v2)).
Proof.
Admitted.

End SimpleTypeSystem.

