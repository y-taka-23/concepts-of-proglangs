Section PolymorphicTypeSystem.
Require Import ZArith.
Open Scope Z_scope.

(* Variables (reused) *)
Inductive Var : Set :=
    | VId : nat -> Var.

(* Expressions (reused) *)
Inductive Exp : Set :=
    | EInt    : Z -> Exp
    | EBool   : bool -> Exp
    | EVar    : Var -> Exp
    | EPlus   : Exp -> Exp -> Exp
    | EMinus  : Exp -> Exp -> Exp
    | ETimes  : Exp -> Exp -> Exp
    | ELt     : Exp -> Exp -> Exp
    | EIf     : Exp -> Exp -> Exp -> Exp
    | ELet    : Var -> Exp -> Exp -> Exp
    | EFun    : Var -> Exp -> Exp
    | EApp    : Exp -> Exp -> Exp
    | ELetRec : Var -> Var -> Exp -> Exp -> Exp
    | ENil    : Exp
    | ECons   : Exp -> Exp -> Exp
    | EMatch  : Exp -> Exp -> Var -> Var -> Exp -> Exp.

(* Values and environments (reused) *)
Inductive Value : Set :=
    | VInt    : Z -> Value
    | VBool   : bool -> Value
    | VFun    : Env -> Var -> Exp -> Value
    | VRecFun : Env -> Var -> Var -> Exp -> Value
    | VNil    : Value
    | VCons   : Value -> Value -> Value
    with Env : Set :=
    | EEmpty  : Env
    | EBind   : Env -> Var -> Value -> Env.

(* Type variables at p.146 *)
Inductive TyVar : Set :=
    | TVId : nat -> TyVar.

Lemma TyVar_eq_dec :
    forall a1 a2 : TyVar, {a1 = a2} + {a1 <> a2}.
Proof.
    intros a1 a2.
    destruct a1 as [i1].
    destruct a2 as [i2].
    destruct (eq_nat_dec i1 i2) as [ H | H ].

        (* Case : i1 = i2 *)
        left.
        subst.
        reflexivity.

        (* Case : i1 <> i2 *)
        right.
        intro F.
        apply H.
        inversion F; subst.
        reflexivity.
Qed.

(* Types at p.146 *)
Inductive Types : Set :=
    | TVar  : TyVar -> Types
    | TBool : Types
    | TInt  : Types
    | TFun  : Types -> Types -> Types
    | TList : Types -> Types.

(* Type scheme at p.146 *)
Inductive TyScheme : Set :=
    | TSType : Types -> TyScheme
    | TSCons : TyVar -> TyScheme -> TyScheme.

(* Type environments at p.146 *)
Inductive TEnv : Set :=
    | TEEmpty : TEnv
    | TEBind  : TEnv -> Var -> TyScheme -> TEnv.

(* Type lookup *)
Inductive has_type : TEnv -> Var -> TyScheme -> Prop :=
    | HT_Bind1 : forall (C : TEnv) (x : Var) (s : TyScheme),
                 has_type (TEBind C x s) x s
    | HT_Bind2 : forall (C : TEnv) (x y : Var) (s s0 : TyScheme),
                 has_type C x s -> y <> x ->
                 has_type (TEBind C y s0) x s.

(* Type substitution *)
Definition TySubst := TyVar -> option Types.
Definition exclude (S : TySubst) (a : TyVar) :=
    fun a0 => if TyVar_eq_dec a0 a then None else S a0.

(* Fig 9.1 *)
Fixpoint subst_type (S : TySubst) (t : Types) : Types :=
    match t with
    | TVar ai => match S ai with
                 | Some ti => ti
                 | None    => TVar ai
                 end
    | TBool   => TBool
    | TInt    => TInt
    | TFun t1 t2 => TFun (subst_type S t1) (subst_type S t2)
    | TList t0   => TList (subst_type S t0)
    end.

(* Substitution for type schemes *)
Fixpoint subst_scheme (S : TySubst) (s : TyScheme) : TyScheme :=
    match s with
    | TSType t    => TSType (subst_type S t)
    | TSCons a s' => TSCons a (subst_scheme (exclude S a) s')
    end.

(* Substitution for type environments *)
Fixpoint subst_env (S : TySubst) (C : TEnv) : TEnv :=
    match C with
    | TEEmpty       => TEEmpty
    | TEBind C' x s => TEBind (subst_env S C') x (subst_scheme S s)
    end.

(* Type expression of type schemes *)
Inductive is_type : TyScheme -> Types -> Prop :=
    | IT_Type : forall t : Types, is_type (TSType t) t
    | IT_Cons : forall (a : TyVar) (s : TyScheme) (t : Types),
                is_type s t -> is_type (TSCons a s) t.

(* Type variables of type schemes *)
Inductive in_vars : TyScheme -> TyVar -> Prop :=
    | IV_Cons1 : forall (s : TyScheme) (a : TyVar),
                 in_vars (TSCons a s) a
    | IV_Cons2 : forall (s : TyScheme) (a a0 : TyVar),
                 in_vars s a -> in_vars (TSCons a0 s) a.

(* Def 9.1 *)
Inductive is_instance : TyScheme -> Types -> Prop :=
    | Instance : forall (S : TySubst) (s : TyScheme) (t t0 : Types),
                 is_type s t0 ->
                 (forall ai : TyVar,
                  in_vars s ai <-> exists ti : Types, S ai = Some ti) ->
                 subst_type S t0 = t ->
                 is_instance s t.

(* Def 9.2 (Fig 9.2, for types) *)
Inductive is_FTV_type : Types -> Types -> Prop :=
    | FTV_Var   : forall (a : TyVar),
                  is_FTV_type (TVar a) (TVar a)
    | FTV_Fun_l : forall (t t1 t2 : Types),
                  is_FTV_type t1 t -> is_FTV_type (TFun t1 t2) t
    | FTV_Fun_r : forall (t t1 t2 : Types),
                  is_FTV_type t2 t -> is_FTV_type (TFun t1 t2) t
    | FTV_List  : forall (t : Types),
                  is_FTV_type (TList t) t.

(* Def 9.2 (Fig 9.2, for type schemes) *)
Inductive is_FTV_scheme : TyScheme -> Types -> Prop :=
    | FTV_Sch1 : forall t t0 : Types,
                 is_FTV_type t0 t -> is_FTV_scheme (TSType t0) t
    | FTV_Sch2 : forall (s : TyScheme) (a : TyVar) (t : Types),
                 is_FTV_scheme s t -> t <> TVar a ->
                 is_FTV_scheme (TSCons a s) t.

(* Def 9.2 (Fig 9.2, for type environments) *)
Inductive is_FTV_env : TEnv -> Types -> Prop :=
    | FTV_Env1 : forall (C : TEnv) (x : Var) (s : TyScheme) (t : Types),
                 is_FTV_env C t -> is_FTV_env (TEBind C x s) t
    | FTV_Env2 : forall (C : TEnv) (x : Var) (s : TyScheme) (t : Types),
                 is_FTV_scheme s t -> is_FTV_env (TEBind C x s) t.

(* Fig 9.3 *)
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
    | T_Var    : forall (C : TEnv) (x : Var) (s : TyScheme) (t : Types),
                 has_type C x s -> is_instance s t ->
                 Typable C (EVar x) t
    | T_Let    : forall (C : TEnv) (e1 e2 : Exp) (x : Var)
                        (s : TyScheme) (t1 t2 : Types),
                 Typable C e1 t1 -> Typable (TEBind C x s) e2 t2 ->
                 is_type s t1 ->
                 (forall a : TyVar, in_vars s a -> ~ is_FTV_env C (TVar a)) ->
                 Typable C (ELet x e1 e2) t2
    | T_Fun    : forall (C : TEnv) (e : Exp) (x : Var) (t1 t2 : Types),
                 Typable (TEBind C x (TSType t1)) e t2 ->
                 Typable C (EFun x e) (TFun t1 t2)
    | T_App    : forall (C : TEnv) (e1 e2 : Exp) (t1 t2 : Types),
                 Typable C e1 (TFun t1 t2) -> Typable C e2 t1 ->
                 Typable C (EApp e1 e2) t2
    | T_LetRec : forall (C : TEnv) (e1 e2 : Exp) (x y : Var)
                        (s : TyScheme) (t t1 t2 : Types),
                 Typable (TEBind (TEBind C x (TSType (TFun t1 t2)))
                                  y (TSType t1)) e1 t2 ->
                 Typable (TEBind C x s) e2 t ->
                 is_type s (TFun t1 t2) ->
                 (forall a : TyVar, in_vars s a -> ~ is_FTV_env C (TVar a)) ->
                 Typable C (ELetRec x y e1 e2) t
    | T_Nil    : forall (C : TEnv) (t : Types),
                 Typable C ENil (TList t)
    | T_Cons   : forall (C : TEnv) (e1 e2 : Exp) (t : Types),
                 Typable C e1 t -> Typable C e2 (TList t) ->
                 Typable C (ECons e1 e2) (TList t)
    | T_Match  : forall (C : TEnv) (e1 e2 e3 : Exp) (x y : Var) (t t' : Types),
                 Typable C e1 (TList t') -> Typable C e2 t ->
                 Typable (TEBind (TEBind C x (TSType t'))
                                  y (TSType (TList t'))) e3 t ->
                 Typable C (EMatch e1 e2 x y e3) t.

(* Lemma 9.3 *)
Lemma Typable_subst_compat :
    forall (S : TySubst) (C : TEnv) (e : Exp) (t : Types),
    Typable C e t -> Typable (subst_env S C) e (subst_type S t).
Proof.
    intros S C e.
    generalize dependent C.
    generalize dependent S.
    induction e as [ i | b | x |
                     e1 He1 e2 He2 | e1 He1 e2 He2 |
                     e1 He1 e2 He2 | e1 He1 e2 He2 |
                     e1 He1 e2 He2 e3 He3 | x e1 He1 e2 He2 | x e He |
                     e1 He1 e2 He2 | x y e1 He1 e2 He2 | |
                     e1 He1 e2 He2 | e1 He1 e2 He2 x y e3 He3 ].

        (* Case : e = EInt i *)
        intros S C t H.
        inversion H; subst.
        simpl.
        apply T_Int.

        (* Case : e = EBool b *)
        intros S C t H.
        inversion H; subst.
        simpl.
        apply T_Bool.

        (* Case : e = EVar x *)
        admit.

        (* Case : e = EPlus e1 e2 *)
        intros S C t H.
        inversion H; subst.
        simpl.
        apply (T_Plus _ _ _ (He1 _ _ _ H3) (He2 _ _ _ H5)).

        (* Case : e = EMinus e1 e2 *)
        intros S C t H.
        inversion H; subst.
        simpl.
        apply (T_Minus _ _ _ (He1 _ _ _ H3) (He2 _ _ _ H5)).

        (* Case : e = ETimes e1 e2 *)
        intros S C t H.
        inversion H; subst.
        simpl.
        apply (T_Times _ _ _ (He1 _ _ _ H3) (He2 _ _ _ H5)).

        (* Case : e = ELt e1 e2 *)
        intros S C t H.
        inversion H; subst.
        simpl.
        apply (T_Lt _ _ _ (He1 _ _ _ H3) (He2 _ _ _ H5)).

        (* Case : e = EIf e1 e2 e3 *)
        intros S C t H.
        inversion H; subst.
        apply (T_If _ _ _ _ _ (He1 _ _ _ H4) (He2 _ _ _ H6) (He3 _ _ _ H7)).

        (* Case : e = ELet x e1 e2 *)
        admit.

        (* Case : e = EFun x e *)
        intros S C t H.
        inversion H; subst.
        simpl.
        apply (T_Fun _ _ _ _ _ (He _ _ _ H4)).

        (* Case : e = EApp e1 e2 *)
        intros S C t H.
        inversion H; subst.
        apply (T_App _ _ _ _ _ (He1 _ _ _ H3) (He2 _ _ _ H5)).

        (* Case : e = ELetRec x y e1 e2 *)
        admit.

        (* Case : e = ENil *)
        intros S C t H.
        inversion H; subst.
        simpl.
        apply T_Nil.

        (* Case : e = ECons e1 e2 *)
        intros S C t H.
        inversion H; subst.
        simpl.
        apply (T_Cons _ _ _ _ (He1 _ _ _ H3) (He2 _ _ _ H5)).

        (* Case : e = EMatch e1 e1 x y e3 *)
        intros S C t H.
        inversion H; subst.
        apply (T_Match _ _ _ _ _ _ _ _
                       (He1 _ _ _ H7) (He2 _ _ _ H8) (He3 _ _ _ H9)).
Qed.

(* Def 9.4 *)
Inductive ValueCompat : Value -> Types -> Prop :=
    | VC_Int    : forall i : Z, ValueCompat (VInt i) TInt
    | VC_Bool   : forall b : bool, ValueCompat (VBool b) TBool
    | VC_Fun    : forall (E : Env) (C : TEnv) (e : Exp)
                         (x : Var) (t1 t2 : Types),
                  EnvCompat E C -> Typable (TEBind C x (TSType t1)) e t2 ->
                  ValueCompat (VFun E x e) (TFun t1 t2)
    | VC_RecFun : forall (E : Env) (C : TEnv) (e : Exp)
                         (x y : Var) (t1 t2 : Types),
                  EnvCompat E C ->
                  Typable (TEBind (TEBind C x (TSType (TFun t1 t2)))
                                            y (TSType t1))
                          e t2 ->
                  ValueCompat (VRecFun E x y e) (TFun t1 t2)
    | VC_Nil    : forall t' : Types, ValueCompat VNil (TList t')
    | VC_Cons   : forall (t' : Types) (v1 v2 : Value),
                  ValueCompat v1 t' -> ValueCompat v2 (TList t') ->
                  ValueCompat (VCons v1 v2) (TList t')
    with EnvCompat : Env -> TEnv -> Prop :=
    | EC_Empty : EnvCompat EEmpty TEEmpty
    | EC_Bind  : forall (E' : Env) (C' : TEnv)
                        (x : Var) (v : Value) (s : TyScheme) (t : Types),
                 EnvCompat E' C' -> ValueCompat v t -> is_type s t ->
                 EnvCompat (EBind E' x v) (TEBind C' x s).

(* Lemma 9.5 *)
Lemma ValueCompat_subst_compat :
    forall (S : TySubst) (v : Value) (t : Types),
    ValueCompat v t -> ValueCompat v (subst_type S t).
Proof.
Admitted.

End PolymorphicTypeSystem.

