Section SimpleTypeSystem.
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

(* Environment lookup (reused) *)
Inductive has_value : Env -> Var -> Value -> Prop :=
    | HV_Bind1 : forall (E : Env) (x : Var) (v : Value),
                 has_value (EBind E x v) x v
    | HV_Bind2 : forall (E : Env) (x y : Var) (v v0 : Value),
                 has_value E x v -> y <> x ->
                 has_value (EBind E y v0) x v.

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

(* Binary operations as relations (reused) *)
Inductive Plus : Z -> Z -> Z -> Prop :=
    | B_Plus : forall i1 i2 i3 : Z, i3 = i1 + i2 -> Plus i1 i2 i3.
Inductive Minus : Z -> Z -> Z -> Prop :=
    | B_Minus : forall i1 i2 i3 : Z, i3 = i1 - i2 -> Minus i1 i2 i3.
Inductive Times : Z -> Z -> Z -> Prop :=
    | B_Times : forall i1 i2 i3 : Z, i3 = i1 * i2 -> Times i1 i2 i3.
Inductive Lt : Z -> Z -> bool -> Prop :=
    | B_Lt : forall (i1 i2 : Z) (b3 : bool), b3 = (i1 <? i2) -> Lt i1 i2 b3.

(* Domains (reuesed) *)
Inductive in_dom : Env -> Var -> Prop :=
    | Dom_EBind1 : forall (E : Env) (x : Var) (v : Value),
                   in_dom (EBind E x v) x
    | Dom_EBind2 : forall (E : Env) (x y : Var) (v : Value),
                   in_dom E x -> in_dom (EBind E y v) x.

(* Evaluation rules (reused) + Fig 8.3, 8.4 and 8.5 *)
Inductive ResultIn : Env -> Exp -> Result -> Prop :=
    | E_Int       : forall (E : Env) (i : Z),
                    ResultIn E (EInt i) (RValue (VInt i))
    | E_Bool      : forall (E : Env) (b : bool),
                    ResultIn E (EBool b) (RValue (VBool b))
    | E_Var       : forall (E : Env) (x : Var) (v : Value),
                    has_value E x v ->
                    ResultIn E (EVar x) (RValue v)
    | E_Plus      : forall (E : Env) (e1 e2 : Exp) (i1 i2 i3 : Z),
                    ResultIn E e1 (RValue (VInt i1)) ->
                    ResultIn E e2 (RValue (VInt i2)) ->
                    Plus i1 i2 i3 ->
                    ResultIn E (EPlus e1 e2) (RValue (VInt i3))
    | E_Minus     : forall (E : Env) (e1 e2 : Exp) (i1 i2 i3 : Z),
                    ResultIn E e1 (RValue (VInt i1)) ->
                    ResultIn E e2 (RValue (VInt i2)) ->
                    Minus i1 i2 i3 ->
                    ResultIn E (EMinus e1 e2) (RValue (VInt i3))
    | E_Times     : forall (E : Env) (e1 e2 : Exp) (i1 i2 i3 : Z),
                    ResultIn E e1 (RValue (VInt i1)) ->
                    ResultIn E e2 (RValue (VInt i2)) ->
                    Times i1 i2 i3 ->
                    ResultIn E (ETimes e1 e2) (RValue (VInt i3))
    | E_Lt        : forall (E : Env) (e1 e2 : Exp) (i1 i2 : Z) (b3 : bool),
                    ResultIn E e1 (RValue (VInt i1)) ->
                    ResultIn E e2 (RValue (VInt i2)) ->
                    Lt i1 i2 b3 ->
                    ResultIn E (ELt e1 e2) (RValue (VBool b3))
    | E_IfT       : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                    ResultIn E e1 (RValue (VBool true)) ->
                    ResultIn E e2 (RValue v) ->
                    ResultIn E (EIf e1 e2 e3) (RValue v)
    | E_IfF       : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                    ResultIn E e1 (RValue (VBool false)) ->
                    ResultIn E e3 (RValue v) ->
                    ResultIn E (EIf e1 e2 e3) (RValue v)
    | E_Let       : forall (E : Env) (e1 e2 : Exp) (x : Var) (v1 v : Value),
                    ResultIn E e1 (RValue v1) ->
                    ResultIn (EBind E x v1) e2 (RValue v) ->
                    ResultIn E (ELet x e1 e2) (RValue v)
    | E_Fun       : forall (E : Env) (x : Var) (e : Exp),
                    ResultIn E (EFun x e) (RValue (VFun E x e))
    | E_App       : forall (E E2 : Env) (e1 e2 e0 : Exp) (x : Var)
                           (v v2 : Value),
                    ResultIn E e1 (RValue (VFun E2 x e0)) ->
                    ResultIn E e2 (RValue v2) ->
                    ResultIn (EBind E2 x v2) e0 (RValue v) ->
                    ResultIn E (EApp e1 e2) (RValue v)
    | E_LetRec    : forall (E : Env) (x y : Var) (e1 e2 : Exp) (v : Value),
                    ResultIn (EBind E x (VRecFun E x y e1)) e2 (RValue v) ->
                    ResultIn E (ELetRec x y e1 e2) (RValue v)
    | E_AppRec    : forall (E E2 : Env) (e1 e2 e0 : Exp) (x y : Var)
                           (v v2 : Value),
                    ResultIn E e1 (RValue (VRecFun E2 x y e0)) ->
                    ResultIn E e2 (RValue v2) ->
                    ResultIn (EBind (EBind E2 x (VRecFun E2 x y e0)) y v2)
                             e0 (RValue v) ->
                    ResultIn E (EApp e1 e2) (RValue v)
    | E_Nil       : forall (E : Env),
                    ResultIn E ENil (RValue VNil)
    | E_Cons      : forall (E : Env) (e1 e2 : Exp) (v1 v2 : Value),
                    ResultIn E e1 (RValue v1) -> ResultIn E e2 (RValue v2) ->
                    ResultIn E (ECons e1 e2) (RValue (VCons v1 v2))
    | E_MatchNil  : forall (E : Env) (e1 e2 e3 : Exp) (v : Value) (x y : Var),
                    ResultIn E e1 (RValue VNil) -> ResultIn E e2 (RValue v) ->
                    ResultIn E (EMatch e1 e2 x y e3) (RValue v)
    | E_MatchCons : forall (E : Env) (e1 e2 e3 : Exp) (x y : Var)
                           (v v1 v2 : Value),
                    ResultIn E e1 (RValue (VCons v1 v2)) ->
                    ResultIn (EBind (EBind E x v1) y v2) e3 (RValue v) ->
                    ResultIn E (EMatch e1 e2 x y e3) (RValue v)
    | E_IfErr1    : forall (E : Env) (e1 e2 e3 : Exp) (r : Result),
                    ResultIn E e1 r ->
                    (forall b : bool, r <> RValue (VBool b)) ->
                    ResultIn E (EIf e1 e2 e3) RError
    | E_IfErr2    : forall (E : Env) (e1 e2 e3 : Exp),
                    ResultIn E e1 (RValue (VBool true)) ->
                    ResultIn E e2 RError ->
                    ResultIn E (EIf e1 e2 e3) RError
    | E_IfErr3    : forall (E : Env) (e1 e2 e3 : Exp),
                    ResultIn E e1 (RValue (VBool false)) ->
                    ResultIn E e3 RError ->
                    ResultIn E (EIf e1 e2 e3) RError
    | E_PlusErr1  : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    ResultIn E (EPlus e1 e2) RError
    | E_PlusErr2  : forall (E : Env) (e1 e2 : Exp) (i1 : Z) (r : Result),
                    ResultIn E e1 (RValue (VInt i1)) ->
                    ResultIn E e2 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    ResultIn E (EPlus e1 e2) RError
    | E_MinusErr1 : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    ResultIn E (EMinus e1 e2) RError
    | E_MinusErr2 : forall (E : Env) (e1 e2 : Exp) (i1 : Z) (r : Result),
                    ResultIn E e1 (RValue (VInt i1)) ->
                    ResultIn E e2 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    ResultIn E (EMinus e1 e2) RError
    | E_TimesErr1 : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    ResultIn E (ETimes e1 e2) RError
    | E_TimesErr2 : forall (E : Env) (e1 e2 : Exp) (i1 : Z) (r : Result),
                    ResultIn E e1 (RValue (VInt i1)) ->
                    ResultIn E e2 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    ResultIn E (ETimes e1 e2) RError
    | E_LtErr1    : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    ResultIn E (ELt e1 e2) RError
    | E_LtErr2    : forall (E : Env) (e1 e2 : Exp) (i1 : Z) (r : Result),
                    ResultIn E e1 (RValue (VInt i1)) ->
                    ResultIn E e2 r -> (forall i : Z, r <> RValue (VInt i)) ->
                    ResultIn E (ELt e1 e2) RError
    | E_VarErr    : forall (E : Env) (x : Var),
                    ~ in_dom E x ->
                    ResultIn E (EVar x) RError
    | E_LetErr1   : forall (E : Env) (e1 e2 : Exp) (x : Var),
                    ResultIn E e1 RError ->
                    ResultIn E (ELet x e1 e2) RError
    | E_LetErr2   : forall (E : Env) (e1 e2 : Exp) (x : Var) (v1 : Value),
                    ResultIn E e1 (RValue v1) ->
                    ResultIn (EBind E x v1) e2 RError ->
                    ResultIn E (ELet x e1 e2) RError
    | E_AppErr1   : forall (E : Env) (e1 e2 : Exp) (r : Result),
                    ResultIn E e1 r ->
                    (forall (E : Env) (x : Var) (e : Exp),
                     r <> RValue (VFun E x e)) ->
                    (forall (E : Env) (x y : Var) (e : Exp),
                     r <> RValue (VRecFun E x y e)) ->
                    ResultIn E (EApp e1 e2) RError
    | E_AppErr2   : forall (E E2 : Env) (e1 e2 e0 : Exp) (x : Var),
                    ResultIn E e1 (RValue (VFun E2 x e0)) ->
                    ResultIn E e2 RError ->
                    ResultIn E (EApp e1 e2) RError
    | E_AppErr3   : forall (E E2 : Env) (e1 e2 e0 : Exp) (x y : Var),
                    ResultIn E e1 (RValue (VRecFun E2 x y e0)) ->
                    ResultIn E e2 RError ->
                    ResultIn E (EApp e1 e2) RError
    | E_AppErr4   : forall (E E2 : Env) (e1 e2 e0 : Exp) (x : Var) (v2 : Value),
                    ResultIn E e1 (RValue (VFun E2 x e0)) ->
                    ResultIn E e2 (RValue v2) ->
                    ResultIn (EBind E x v2) e0 RError ->
                    ResultIn E (EApp e1 e2) RError
    | E_AppErr5   : forall (E E2 : Env) (e1 e2 e0 : Exp)
                           (x y : Var) (v2 : Value),
                    ResultIn E e1 (RValue (VRecFun E2 x y e0)) ->
                    ResultIn E e2 (RValue v2) ->
                    ResultIn (EBind (EBind E x (VRecFun E2 x y e0)) y v2)
                             e0 RError->
                    ResultIn E (EApp e1 e2) RError
    | E_LetRecErr : forall (E : Env) (e1 e2 : Exp) (x y : Var),
                    ResultIn (EBind E x (VRecFun E x y e1)) e2 RError ->
                    ResultIn E (ELetRec x y e1 e2) RError
    | E_ConsErr1  : forall (E : Env) (e1 e2 : Exp),
                    ResultIn E e1 RError ->
                    ResultIn E (ECons e1 e2) RError
    | E_ConsErr2  : forall (E : Env) (e1 e2 : Exp) (v1 : Value),
                    ResultIn E e1 (RValue v1) -> ResultIn E e2 RError ->
                    ResultIn E (ECons e1 e2) RError
    | E_MatchErr1 : forall (E : Env) (e1 e2 e3 : Exp) (x y : Var) (r : Result),
                    ResultIn E e1 r -> r <> RValue VNil ->
                    (forall v1 v2 : Value, r <> RValue (VCons v1 v2)) ->
                    ResultIn E (EMatch e1 e2 x y e3) RError
    | E_MatchErr2 : forall (E : Env) (e1 e2 e3 : Exp) (x y : Var),
                    ResultIn E e1 (RValue VNil) -> ResultIn E e2 RError ->
                    ResultIn E (EMatch e1 e2 x y e3) RError
    | E_MatchErr3 : forall (E : Env) (e1 e2 e3 : Exp)
                           (x y : Var) (v1 v2 : Value),
                    ResultIn E e1 (RValue (VCons v1 v2)) ->
                    ResultIn (EBind (EBind E x v1) y v2) e3 RError ->
                    ResultIn E (EMatch e1 e2 x y e3) RError.

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
Admitted.

(* Theorem 8.1 (1) *)
Theorem Typable_safe_int :
    forall (e : Exp) (r : Result),
    Typable TEEmpty e TInt -> ResultIn EEmpty e r ->
    exists i : Z, r = RValue (VInt i).
Proof.
Admitted.

(* Theorem 8.1 (2) *)
Theorem Typable_safe_bool :
    forall (e : Exp) (r : Result),
    Typable TEEmpty e TBool -> ResultIn EEmpty e r ->
    exists b : bool, r = RValue (VBool b).
Proof.
Admitted.

(* Theorem 8.1 (3) *)
Theorem Typable_safe_fun :
    forall (e : Exp) (r : Result) (t1 t2 : Types),
    Typable TEEmpty e (TFun t1 t2) -> ResultIn EEmpty e r ->
    exists (E : Env) (x : Var) (e : Exp), r = RValue (VFun E x e) \/
         exists (E : Env) (x y : Var) (e : Exp), r = RValue (VRecFun E x y e).
Proof.
Admitted.

(* Theorem 8.1 (4) *)
Theorem Typable_safe_list :
    forall (e : Exp) (r : Result) (t : Types),
    Typable TEEmpty e (TList t) -> ResultIn EEmpty e r ->
    r = RValue VNil \/ exists v1 v2 : Value, r = RValue (VCons v1 v2).
Proof.
Admitted.

End SimpleTypeSystem.

