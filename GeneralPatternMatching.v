Section GeneralPatternMatching.
Require Import ZArith.
Open Scope Z_scope.

(* Variables (reused) *)
Inductive Var : Set :=
    | VId : nat -> Var.

(* Patterns at p.114 *)
Inductive Pat : Set :=
    | PVar  : Var -> Pat
    | PNil  : Pat
    | PCons : Pat -> Pat -> Pat
    | PWild : Pat.

(* Expressions at p.114 *)
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
    | EMatch  : Exp -> Clauses -> Exp
    with Clauses : Set :=
    | COne  : Pat -> Exp -> Clauses
    | CCons : Pat -> Exp -> Clauses -> Clauses.

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

Inductive Bound : Env -> Var -> Prop :=
    | B_Bind1 : forall (E : Env) (x : Var) (v : Value),
                Bound (EBind E x v) x
    | B_Bind2 : forall (E : Env) (x y : Var) (v : Value),
                Bound E x ->
                Bound (EBind E y v) x.

(* Merger of two disjoint environments *)
Inductive MergeTo : Env -> Env -> Env -> Prop :=
    | Mer_Empty  : MergeTo EEmpty EEmpty EEmpty
    | Mer_Bind_l : forall (E : Env) (x : Var) (v : Value),
                   ~ Bound E x ->
                   MergeTo (EBind E x v) EEmpty (EBind E x v)
    | Mer_Bind_r : forall (E E1 E2 : Env) (x : Var) (v : Value),
                   MergeTo E1 E2 E -> ~ Bound E1 x -> ~ Bound E2 x ->
                   MergeTo E1 (EBind E2 x v) (EBind E x v).

(* Success of pattern match at p.115 *)
Inductive Match : Pat -> Value -> Env -> Prop :=
    | M_Var  : forall (x : Var) (v : Value),
               Match (PVar x) v (EBind EEmpty x v)
    | M_Nil  : Match PNil VNil EEmpty
    | M_Cons : forall (p1 p2 : Pat) (v1 v2 : Value) (E E1 E2 : Env),
               Match p1 v1 E1 -> Match p2 v2 E2 -> MergeTo E1 E2 E ->
               Match (PCons p1 p2) (VCons v1 v2) E
    | M_Wild : forall v : Value,
               Match PWild v EEmpty.

(* Failure of pattern match at p.116 *)
Inductive NotMatch : Pat -> Value -> Prop :=
    | NM_ConsNil   : forall v1 v2 : Value,
                     NotMatch PNil (VCons v1 v2)
    | NM_NilCons   : forall p1 p2 : Pat,
                     NotMatch (PCons p1 p2) VNil
    | NM_ConsConsL : forall (p1 p2 : Pat) (v1 v2 : Value),
                     NotMatch p1 v1 ->
                     NotMatch (PCons p1 p2) (VCons v1 v2)
    | NM_ConsConsR : forall (p1 p2 : Pat) (v1 v2 : Value),
                     NotMatch p2 v2 ->
                     NotMatch (PCons p1 p2) (VCons v1 v2).

(* Binary operations as relations (reused) *)
Inductive Plus : Z -> Z -> Z -> Prop :=
    | B_Plus : forall i1 i2 i3 : Z, i3 = i1 + i2 -> Plus i1 i2 i3.
Inductive Minus : Z -> Z -> Z -> Prop :=
    | B_Minus : forall i1 i2 i3 : Z, i3 = i1 - i2 -> Minus i1 i2 i3.
Inductive Times : Z -> Z -> Z -> Prop :=
    | B_Times : forall i1 i2 i3 : Z, i3 = i1 * i2 -> Times i1 i2 i3.
Inductive Lt : Z -> Z -> bool -> Prop :=
    | B_Lt : forall (i1 i2 : Z) (b3 : bool), b3 = (i1 <? i2) -> Lt i1 i2 b3.

(* Concatination of two environments (not necessarily disjoint) *)
Inductive ConcatTo : Env -> Env -> Env -> Prop :=
    | Con_Empty : forall E : Env, ConcatTo E EEmpty E
    | Con_Bind  : forall (E E1 E2 : Env) (x : Var) (v : Value),
                  ConcatTo E1 E2 E ->
                  ConcatTo E1 (EBind E2 x v) (EBind E x v).

(* Environment lookup (reused) *)
Inductive has_value : Env -> Var -> Value -> Prop :=
    | HV_Bind1 : forall (E : Env) (x : Var) (v : Value),
                 has_value (EBind E x v) x v
    | HV_Bind2 : forall (E : Env) (x y : Var) (v v0 : Value),
                 has_value E x v -> y <> x ->
                 has_value (EBind E y v0) x v.

(* Evaluation rules at p.117 *)
Inductive EvalTo : Env -> Exp -> Value -> Prop :=
    | E_Int     : forall (E : Env) (i : Z),
                  EvalTo E (EInt i) (VInt i)
    | E_Bool    : forall (E : Env) (b : bool),
                  EvalTo E (EBool b) (VBool b)
    | E_Var     : forall (E : Env) (x : Var) (v : Value),
                  has_value E x v ->
                  EvalTo E (EVar x) v
    | E_Plus    : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                  EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                  Plus i1 i2 i3 ->
                  EvalTo E (EPlus e1 e2) (VInt i3)
    | E_Minus   : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                  EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                  Minus i1 i2 i3 ->
                  EvalTo E (EMinus e1 e2) (VInt i3)
    | E_Times   : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                  EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                  Times i1 i2 i3 ->
                  EvalTo E (ETimes e1 e2) (VInt i3)
    | E_Lt      : forall (E : Env) (e1 e2 : Exp) (i1 i2 : Z) (b3 : bool),
                  EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                  Lt i1 i2 b3 ->
                  EvalTo E (ELt e1 e2) (VBool b3)
    | E_IfT     : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                  EvalTo E e1 (VBool true) -> EvalTo E e2 v ->
                  EvalTo E (EIf e1 e2 e3) v
    | E_IfF     : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                  EvalTo E e1 (VBool false) -> EvalTo E e3 v ->
                  EvalTo E (EIf e1 e2 e3) v
    | E_Let     : forall (E : Env) (e1 e2 : Exp) (x : Var) (v1 v : Value),
                  EvalTo E e1 v1 -> EvalTo (EBind E x v1) e2 v ->
                  EvalTo E (ELet x e1 e2) v
    | E_Fun     : forall (E : Env) (x : Var) (e : Exp),
                  EvalTo E (EFun x e) (VFun E x e)
    | E_App     : forall (E E2 : Env) (e1 e2 e0 : Exp) (x : Var)
                         (v v2 : Value),
                  EvalTo E e1 (VFun E2 x e0) -> EvalTo E e2 v2 ->
                  EvalTo (EBind E2 x v2) e0 v ->
                  EvalTo E (EApp e1 e2) v
    | E_LetRec  : forall (E : Env) (x y : Var) (e1 e2 : Exp) (v : Value),
                  EvalTo (EBind E x (VRecFun E x y e1)) e2 v ->
                  EvalTo E (ELetRec x y e1 e2) v
    | E_AppRec  : forall (E E2 : Env) (e1 e2 e0 : Exp) (x y : Var)
                         (v v2 : Value),
                  EvalTo E e1 (VRecFun E2 x y e0) -> EvalTo E e2 v2 ->
                  EvalTo (EBind (EBind E2 x (VRecFun E2 x y e0)) y v2) e0 v ->
                  EvalTo E (EApp e1 e2) v
    | E_Nil     : forall (E : Env),
                  EvalTo E ENil VNil
    | E_Cons    : forall (E : Env) (e1 e2 : Exp) (v1 v2 : Value),
                  EvalTo E e1 v1 -> EvalTo E e2 v2 ->
                  EvalTo E (ECons e1 e2) (VCons v1 v2)
    | E_MatchM1 : forall (E E1 E2 : Env) (e e0 : Exp) (v v' : Value) (p : Pat),
                  EvalTo E e0 v -> Match p v E1 ->
                  ConcatTo E E1 E2 -> EvalTo E2 e v' ->
                  EvalTo E (EMatch e0 (COne p e)) v'
    | E_MatchM2 : forall (E E1 E2 : Env) (e e0 : Exp) (v v' : Value)
                         (p : Pat) (c : Clauses),
                  EvalTo E e0 v -> Match p v E1 ->
                  ConcatTo E E1 E2 -> EvalTo E2 e v' ->
                  EvalTo E (EMatch e0 (CCons p e c)) v'
    | E_MatchN  : forall (E : Env) (e e0 : Exp) (v v' : Value)
                         (p : Pat) (c : Clauses),
                  EvalTo E e0 v -> NotMatch p v -> EvalTo E (EMatch e0 c) v' ->
                  EvalTo E (EMatch e0 (CCons p e c)) v'.

End GeneralPatternMatching.

