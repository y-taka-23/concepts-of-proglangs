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

(* Fig 9.1 *)
Definition TySubst := TyVar -> option Types.
Inductive subst_type : TySubst -> Types -> Types -> Prop :=
    | Sub_Var1 : forall (S : TySubst) (ai : TyVar) (ti : Types),
                 S ai = Some ti -> subst_type S (TVar ai) ti
    | Sub_Var2 : forall (S : TySubst) (a : TyVar),
                 S a = None -> subst_type S (TVar a) (TVar a)
    | Sub_Bool : forall S : TySubst, subst_type S TBool TBool
    | Sub_Int  : forall S : TySubst, subst_type S TInt TInt
    | Sub_Fun  : forall (S : TySubst) (t1 t2 t1' t2': Types),
                 subst_type S t1 t1' -> subst_type S t2 t2' ->
                 subst_type S (TFun t1 t2) (TFun t1' t2')
    | Sub_List : forall (S : TySubst) (t0 t0': Types),
                 subst_type S t0 t0' -> subst_type S (TList t0) (TList t0').

(* Def 9.1 *)
Inductive is_instance : TyScheme -> Types -> Prop :=
    | Inst : forall (s : TyScheme) (S : TySubst) (t t0 : Types),
             is_type s t0 -> subst_type S t0 t -> is_instance s t.

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

Inductive no_conflict : TySubst -> TyVar -> Prop :=
    | NoCon : forall (S : TySubst) (a : TyVar),
              S a = None ->
              (forall (bi : TyVar) (ti : Types),
               S bi = Some ti -> ~ is_FTV_type ti (TVar a)) ->
              no_conflict S a.

(* Substitution for type schemes *)
Inductive subst_scheme : TySubst -> TyScheme -> TyScheme -> Prop :=
    | Sub_Type : forall (S : TySubst) (t t' : Types),
                 subst_type S t t' -> subst_scheme S (TSType t) (TSType t')
    | Sub_Cons : forall (S : TySubst) (a : TyVar) (s s' : TyScheme),
                 subst_scheme S s s' -> no_conflict S a ->
                 subst_scheme S (TSCons a s) (TSCons a s').

(* Substitution for type environments *)
Inductive subst_env : TySubst -> TEnv -> TEnv -> Prop :=
    | Sub_Empty : forall S : TySubst, subst_env S TEEmpty TEEmpty
    | Sub_Bind  : forall (S : TySubst) (C C' : TEnv) (x : Var)
                         (s s': TyScheme),
                  subst_env S C C' -> subst_scheme S s s' ->
                  subst_env S (TEBind C x s) (TEBind C' x s').

Lemma subst_type_total :
    forall (S : TySubst) (t : Types),
    exists t' : Types, subst_type S t t'.
Proof.
    intros S t.
    induction t as [ a | | | t1 Ht1 t2 Ht2 | t0 Ht0 ].

        (* Case : t = TVar a *)
        remember (S a) as Ha.
        destruct Ha as [ ti | ].

            (* Case : S a = Some ti *)
            exists ti. Print eq_sym.
            apply (Sub_Var1 _ _ _ (eq_sym HeqHa)).

            (* Case : S a = None *)
            exists (TVar a).
            apply (Sub_Var2 _ _ (eq_sym HeqHa)).

        (* Case : t = TBool *)
        exists TBool.
        apply Sub_Bool.

        (* Case : t = TInt *)
        exists TInt.
        apply Sub_Int.

        (* Case : t = TFun t1 t2 *)
        destruct Ht1 as [t1' Ht1'].
        destruct Ht2 as [t2' Ht2'].
        exists (TFun t1' t2').
        apply (Sub_Fun _ _ _ _ _ Ht1' Ht2').

        (* Case : t = TList t0 *)
        destruct Ht0 as [t0' Ht0'].
        exists (TList t0').
        apply (Sub_List _ _ _ Ht0').
Qed.

(* Lemma 9.3 *)
Lemma Typable_subst_compat :
    forall (C C' : TEnv) (e : Exp) (t t' : Types) (S : TySubst),
    Typable C e t -> subst_env S C C' -> subst_type S t t' ->
    Typable C' e t'.
Proof.
    intros C C' e.
    generalize dependent C'.
    generalize dependent C.
    induction e as [ i | b | x |
                     e1 He1 e2 He2 | e1 He1 e2 He2 |
                     e1 He1 e2 He2 | e1 He1 e2 He2 |
                     e1 He1 e2 He2 e3 He3 | x e1 He1 e2 He2 | x e1 He1 |
                     e1 He1 e2 He2 | x y e1 He1 e2 He2 | |
                     e1 He1 e2 He2 | e1 He1 e2 He2 x y e3 He3 ].

        (* Case : e = EInt i *)
        intros C C' t t' S Ht Hse Hst.
        inversion Ht; subst.
        inversion Hst; subst.
        apply T_Int.

        (* Case : e = EBool b *)
        intros C C' t t' S Ht Hse Hst.
        inversion Ht; subst.
        inversion Hst; subst.
        apply T_Bool.

        (* Case : e = EVar x *)
        admit.

        (* Case : e = EPlus e1 e2 *)
        intros C C' t t' S Ht Hes Hst.
        inversion Ht; subst.
        inversion Hst; subst.
        apply (T_Plus _ _ _ (He1 _ _ _ _ _ H2 Hes (Sub_Int _))
                            (He2 _ _ _ _ _ H4 Hes (Sub_Int _))).

        (* Case : e = EMinus e1 e2 *)
        intros C C' t t' S Ht Hes Hst.
        inversion Ht; subst.
        inversion Hst; subst.
        apply (T_Minus _ _ _ (He1 _ _ _ _ _ H2 Hes (Sub_Int _))
                             (He2 _ _ _ _ _ H4 Hes (Sub_Int _))).

        (* Case : e = ETimes e1 e2 *)
        intros C C' t t' S Ht Hes Hst.
        inversion Ht; subst.
        inversion Hst; subst.
        apply (T_Times _ _ _ (He1 _ _ _ _ _ H2 Hes (Sub_Int _))
                             (He2 _ _ _ _ _ H4 Hes (Sub_Int _))).

        (* Case : e = ELt e1 e2 *)
        intros C C' t t' S Ht Hes Hst.
        inversion Ht; subst.
        inversion Hst; subst.
        apply (T_Lt _ _ _ (He1 _ _ _ _ _ H2 Hes (Sub_Int _))
                          (He2 _ _ _ _ _ H4 Hes (Sub_Int _))).

        (* Case : e = EIf e1 e2 e3 *)
        intros C C' t t' S Ht Hse Hst.
        inversion Ht; subst.
        apply (T_If _ _ _ _ _ (He1 _ _ _ _ _ H3 Hse (Sub_Bool _))
                              (He2 _ _ _ _ _ H5 Hse Hst)
                              (He3 _ _ _ _ _ H6 Hse Hst)).

        (* Case : e = ELet x e1 e2 *)
        admit.

        (* Case : e = EFun x e1 *)
        intros C C' t t' S Ht Hse Hst.
        inversion Ht; subst.
        inversion Hst; subst.
        apply T_Fun.
        refine (He1 _ _ _ _ _ H3 _ H5).
        apply (Sub_Bind _ _ _ _ _ _ Hse (Sub_Type _ _ _ H2)).

        (* Case : e = EApp e1 e2 *)
        intros C C' t t' S Ht Hse Hst.
        inversion Ht; subst.
        remember (subst_type_total S t1) as Ht1'; clear HeqHt1'.
        destruct Ht1' as [t1' Ht1'].
        apply (T_App _ _ _ _ _
                     (He1 _ _ _ _ _ H2 Hse (Sub_Fun _ _ _ _ _ Ht1' Hst))
                     (He2 _ _ _ _ _ H4 Hse Ht1')).

        (* Case : e = ELetRec x y e1 e2 *)
        admit.

        (* Case : e = ENil *)
        intros C C' t t' S Ht Hse Hst.
        inversion Ht; subst.
        inversion Hst; subst.
        apply T_Nil.

        (* Case : e = ECons e1 e2 *)
        intros C C' t t' S Ht Hse Hst.
        inversion Ht; subst.
        inversion Hst; subst.
        apply (T_Cons _ _ _ _ (He1 _ _ _ _ _ H2 Hse H1)
                              (He2 _ _ _ _ _ H4 Hse (Sub_List _ _ _ H1))).

        (* Case : e = EMatch x y e1 e2 e3 *)
        admit.
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
    forall (S : TySubst) (v : Value) (t t' : Types),
    ValueCompat v t -> subst_type S t t' -> ValueCompat v t'.
Proof.
    intros S v.
    induction v as [ i | b | E x e0 | E x y e0 | | v1 Hv1 v2 Hv2 ].

        (* Case : v = VInt i *)
        intros t t' Hvc Hst.
        inversion Hvc; subst.
        inversion Hst; subst.
        apply VC_Int.

        (* Case : v = VBool b *)
        intros t t' Hvc Hst.
        inversion Hvc; subst.
        inversion Hst; subst.
        apply VC_Bool.

        (* Case : v = VFun E x e0 *)
        admit.

        (* Case : v = VRecFun E x y e0 *)
        admit.

        (* Case : v = VNil *)
        intros t t' Hvc Hst.
        inversion Hvc; subst.
        inversion Hst; subst.
        apply VC_Nil.

        (* Case : v = VCons v1 v2 *)
        intros t t' Hvc Hst.
        inversion Hvc; subst.
        inversion Hst; subst.
        apply (VC_Cons _ _ _ (Hv1 _ _ H1 H2) (Hv2 _ _ H3 (Sub_List _ _ _ H2))).
Qed.

End PolymorphicTypeSystem.

