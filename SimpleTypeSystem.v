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

(* Optional type for values *)
Inductive Result : Set :=
    | RValue : Value -> Result
    | RError : Result.

(* Domains (reuesed) *)
Inductive in_dom : Env -> Var -> Prop :=
    | Dom_EBind1 : forall (E : Env) (x : Var) (v : Value),
                   in_dom (EBind E x v) x
    | Dom_EBind2 : forall (E : Env) (x y : Var) (v : Value),
                   in_dom E x -> in_dom (EBind E y v) x.

(* Fig 8.3, 8.4 and 8.5 *)
Inductive Error : Env -> Exp -> Prop :=
    | E_IfErr1    : forall (E : Env) (e1 e2 e3 : Exp) (r : Result),
                    ResultIn E e1 r ->
                    (forall b : bool, r <> RValue (VBool b)) ->
                    Error E (EIf e1 e2 e3)
    | E_IfErr2    : forall (E : Env) (e1 e2 e3 : Exp),
                    EvalTo E e1 (VBool true) -> Error E e2 ->
                    Error E (EIf e1 e2 e3)
    | E_IfErr3    : forall (E : Env) (e1 e2 e3 : Exp),
                    EvalTo E e1 (VBool false) -> Error E e3 ->
                    Error E (EIf e1 e2 e3)
    | E_PlusErr1  : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    Error E (EPlus e1 e2)
    | E_PlusErr2  : forall (E : Env) (e1 e2 : Exp) (i1 : Z) (r : Result),
                    EvalTo E e1 (VInt i1) -> ResultIn E e2 r ->
                    (forall i : Z, r <> RValue (VInt i)) ->
                    Error E (EPlus e1 e2)
    | E_MinusErr1 : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    Error E (EMinus e1 e2)
    | E_MinusErr2 : forall (E : Env) (e1 e2 : Exp) (i1 : Z) (r : Result),
                    EvalTo E e1 (VInt i1) -> ResultIn E e2 r ->
                    (forall i : Z, r <> RValue (VInt i)) ->
                    Error E (EMinus e1 e2)
    | E_TimesErr1 : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    Error E (ETimes e1 e2)
    | E_TimesErr2 : forall (E : Env) (e1 e2 : Exp) (i1 : Z) (r : Result),
                    EvalTo E e1 (VInt i1) -> ResultIn E e2 r ->
                    (forall i : Z, r <> RValue (VInt i)) ->
                    Error E (ETimes e1 e2)
    | E_LtErr1    : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    Error E (ELt e1 e2)
    | E_LtErr2    : forall (E : Env) (e1 e2 : Exp) (i1 : Z) (r : Result),
                    EvalTo E e1 (VInt i1) -> ResultIn E e2 r ->
                    (forall i : Z, r <> RValue (VInt i)) ->
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
    | E_AppErr1   : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r ->
                    (forall (E : Env) (x : Var) (e : Exp),
                     r <> RValue (VFun E x e)) ->
                    (forall (E : Env) (x y : Var) (e : Exp),
                     r <> RValue (VRecFun E x y e)) ->
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
    | E_MatchErr1 : forall (E : Env) (e1 e2 e3 : Exp) (x y : Var) (r : Result),
                    ResultIn E e1 r -> r <> RValue VNil ->
                    (forall v1 v2 : Value, r <> RValue (VCons v1 v2)) ->
                    Error E (EMatch e1 e2 x y e3)
    | E_MatchErr2 : forall (E : Env) (e1 e2 e3 : Exp) (x y : Var),
                    EvalTo E e1 VNil -> Error E e2 ->
                    Error E (EMatch e1 e2 x y e3)
    | E_MatchErr3 : forall (E : Env) (e1 e2 e3 : Exp)
                           (x y : Var) (v1 v2 : Value),
                    EvalTo E e1 (VCons v1 v2) ->
                    Error (EBind (EBind E x v1) y v2) e3 ->
                    Error E (EMatch e1 e2 x y e3)
    with ResultIn : Env -> Exp -> Result -> Prop :=
    | R_Value : forall (E : Env) (e : Exp) (v : Value),
                EvalTo E e v -> ResultIn E e (RValue v)
    | R_Error : forall (E : Env) (e : Exp),
                Error E e -> ResultIn E e RError.

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

(* Theorem 8.3 *)
Theorem type_safety_general :
    forall (E : Env) (C : TEnv) (e : Exp) (r : Result) (t : Types),
    Typable C e t -> ResultIn E e r -> EnvCompat E C ->
    exists v : Value, r = RValue v /\ ValueCompat v t.
Proof.
    intros E C e r t Ht Hr.
    generalize dependent t.
    generalize dependent C.
    induction Hr as [ E e v He | E e He ].

        (* Case : Hr is from H_Value *)
        induction He as [ E i | E b | E x v Hv |
                          E e1 e2 i1 i2 i3 He1 He1' He2 He2' Hp |
                          E e1 e2 i1 i2 i3 He1 He1' He2 He2' Hm |
                          E e1 e2 i1 i2 i3 He1 He1' He2 He2' Htm |
                          E e1 e2 i1 i2 b3 He1 He1' He2 He2' Hl |
                          E e1 e2 e3 v He1 He1' He2 He2' |
                          E e1 e2 e3 v He1 He1' He3 He3' |
                          E e1 e2 x v' v He1 He1' He2 He2' | E x e |
                          E E2 e1 e2 e0 x v v2 He1 He1' He2 He2' He0 He0' |
                          E x y e1 e2 v He2 He2' |
                          E E2 e1 e2 e0 x y v v0 He1 He1' He2 He2' He0 He0' |
                          E | E e1 e2 v1 v2 He1 He1' He2 He2' |
                          E e1 e2 e3 v x y He1 He1' He2 He2' |
                          E e1 e2 e3 x y v v1 v2 He1 He1' He3 He3' ].

            (* Case : He is from E_Int *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VInt i).
            apply (conj eq_refl (VC_Int _)).

            (* Case : He is from E_Bool *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VBool b).
            apply (conj eq_refl (VC_Bool _)).

            (* Case : He is from E_Var *)
            admit.

            (* Case : He is from E_Plus *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VInt i3).
            apply (conj eq_refl (VC_Int _)).

            (* Case : He is from E_Minus *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VInt i3).
            apply (conj eq_refl (VC_Int _)).

            (* Case : He is from E_Times *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VInt i3).
            apply (conj eq_refl (VC_Int _)).

            (* Case : He is from E_Lt *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VBool b3).
            apply (conj eq_refl (VC_Bool _)).

            (* Case : He is from E_IfT *)
            intros C t Ht HC.
            inversion Ht; subst.
            apply (He2' _ _ H5 HC).

            (* Case : He is from E_IfF *)
            intros C t Ht HC.
            inversion Ht; subst.
            apply (He3' _ _ H6 HC).

            (* Case : He is from E_Let *)
            intros C t Ht HC.
            inversion Ht; subst.
            specialize (He1' _ _ H4 HC).
            destruct He1' as [v1 [Hv1 He1']].
            inversion Hv1; subst.
            apply (He2' _ _ H5 (EC_Bind _ _ _ _ _ HC He1')).

            (* Case : He is from E_Fun *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists (VFun E x e).
            apply (conj eq_refl (VC_Fun _ _ _ _ _ _ HC H3)).

            (* Case : He is from E_App *)
            admit.

            (* Case : He is from E_LetRec *)
            admit.

            (* Case : He is from E_RecApp *)
            admit.

            (* Case : He is from E_Nil *)
            intros C t Ht HC.
            inversion Ht; subst.
            exists VNil.
            apply (conj eq_refl (VC_Nil _)).

            (* Case : He is from E_Cons *)
            intros C t Ht HC.
            inversion Ht; subst.
            specialize (He1' _ _ H2 HC).
            destruct He1' as [v1' [Hv1' He1']].
            inversion Hv1'; subst.
            specialize (He2' _ _ H4 HC).
            destruct He2' as [v2' [Hv2' He2']].
            inversion Hv2'; subst.
            exists (VCons v1' v2').
            apply (conj eq_refl (VC_Cons _ _ _ He1' He2')).

            (* Case : He is from E_MatchNil *)
            intros C t Ht HC.
            inversion Ht; subst.
            apply (He2' _ _ H7 HC).

            (* Case : He is from E_MatchCons *)
            intros C t Ht HC.
            inversion Ht; subst.
            specialize (He1' _ _ H6 HC).
            destruct He1' as [v1' [Hv1' He1']].
            inversion Hv1'; subst.
            inversion He1'; subst.
            apply (He3' _ _ H8 (EC_Bind _ _ _ _ _ (EC_Bind _ _ _ _ _ HC H2) H3)).

        (* Case : Hh is from H_Error *)
        admit.
Qed.

(* Theorem 8.1 *)
Theorem type_safety :
    forall (e : Exp) (t t1 t2 t' : Types) (v : Value) (r : Result),
    Typable TEEmpty e t -> ResultIn EEmpty e r ->
    (t = TInt ->
     exists i : Z, ResultIn EEmpty e (RValue (VInt i))) /\
    (t = TBool ->
     exists b : bool, ResultIn EEmpty e (RValue (VBool b))) /\
    (t = TFun t1 t2 ->
     exists (E : Env) (x : Var) (e : Exp),
         ResultIn EEmpty e (RValue (VFun E x e)) \/
     exists (E : Env) (x y : Var) (e : Exp),
         ResultIn EEmpty e (RValue (VRecFun E x y e))) /\
    (t = TList t' ->
     EvalTo EEmpty e VNil \/
     exists v1 v2 : Value, ResultIn EEmpty e (RValue (VCons v1 v2))).
Proof.
Admitted.

End SimpleTypeSystem.

