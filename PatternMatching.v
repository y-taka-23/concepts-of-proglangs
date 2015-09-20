Section PatternMatching.
Require Import ZArith.
Open Scope Z_scope.

(* Variables (reused) *)
Inductive Var : Set :=
    | VId : nat -> Var.

(* Expressions at p.111 *)
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

(* Values and environments at p.111 *)
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

(* Binary operations as relations (reused) *)
Inductive Plus : Z -> Z -> Z -> Prop :=
    | B_Plus : forall i1 i2 i3 : Z, i3 = i1 + i2 -> Plus i1 i2 i3.
Inductive Minus : Z -> Z -> Z -> Prop :=
    | B_Minus : forall i1 i2 i3 : Z, i3 = i1 - i2 -> Minus i1 i2 i3.
Inductive Times : Z -> Z -> Z -> Prop :=
    | B_Times : forall i1 i2 i3 : Z, i3 = i1 * i2 -> Times i1 i2 i3.
Inductive Lt : Z -> Z -> bool -> Prop :=
    | B_Lt : forall (i1 i2 : Z) (b3 : bool), b3 = (i1 <? i2) -> Lt i1 i2 b3.

(* Evaluation rules at p.111 *)
Inductive EvalTo : Env -> Exp -> Value -> Prop :=
    | E_Int       : forall (E : Env) (i : Z),
                    EvalTo E (EInt i) (VInt i)
    | E_Bool      : forall (E : Env) (b : bool),
                    EvalTo E (EBool b) (VBool b)
    | E_Var1      : forall (E : Env) (x : Var) (v : Value),
                    EvalTo (EBind E x v) (EVar x) v
    | E_Var2      : forall (E : Env) (x y : Var) (v1 v2 : Value),
                    x <> y -> EvalTo E (EVar x) v2 ->
                    EvalTo (EBind E y v1) (EVar x) v2
    | E_Plus      : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                    EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                    Plus i1 i2 i3 ->
                    EvalTo E (EPlus e1 e2) (VInt i3)
    | E_Minus     : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                    EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                    Minus i1 i2 i3 ->
                    EvalTo E (EMinus e1 e2) (VInt i3)
    | E_Times     : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                    EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                    Times i1 i2 i3 ->
                    EvalTo E (ETimes e1 e2) (VInt i3)
    | E_Lt        : forall (E : Env) (e1 e2 : Exp) (i1 i2 : Z) (b3 : bool),
                    EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                    Lt i1 i2 b3 ->
                    EvalTo E (ELt e1 e2) (VBool b3)
    | E_IfT       : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                    EvalTo E e1 (VBool true) -> EvalTo E e2 v ->
                    EvalTo E (EIf e1 e2 e3) v
    | E_IfF       : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                    EvalTo E e1 (VBool false) -> EvalTo E e3 v ->
                    EvalTo E (EIf e1 e2 e3) v
    | E_Let       : forall (E : Env) (e1 e2 : Exp) (x : Var) (v1 v : Value),
                    EvalTo E e1 v1 -> EvalTo (EBind E x v1) e2 v ->
                    EvalTo E (ELet x e1 e2) v
    | E_Fun       : forall (E : Env) (x : Var) (e : Exp),
                    EvalTo E (EFun x e) (VFun E x e)
    | E_App       : forall (E E2 : Env) (e1 e2 e0 : Exp) (x : Var)
                           (v v2 : Value),
                    EvalTo E e1 (VFun E2 x e0) -> EvalTo E e2 v2 ->
                    EvalTo (EBind E2 x v2) e0 v ->
                    EvalTo E (EApp e1 e2) v
    | E_LetRec    : forall (E : Env) (x y : Var) (e1 e2 : Exp) (v : Value),
                    EvalTo (EBind E x (VRecFun E x y e1)) e2 v ->
                    EvalTo E (ELetRec x y e1 e2) v
    | E_AppRec    : forall (E E2 : Env) (e1 e2 e0 : Exp) (x y : Var)
                           (v v2 : Value),
                    EvalTo E e1 (VRecFun E2 x y e0) -> EvalTo E e2 v2 ->
                    EvalTo (EBind (EBind E2 x (VRecFun E2 x y e0)) y v2) e0 v ->
                    EvalTo E (EApp e1 e2) v
    | E_Nil       : forall (E : Env),
                    EvalTo E ENil VNil
    | E_Cons      : forall (E : Env) (e1 e2 : Exp) (v1 v2 : Value),
                    EvalTo E e1 v1 -> EvalTo E e2 v2 ->
                    EvalTo E (ECons e1 e2) (VCons v1 v2)
    | E_MatchNil  : forall (E : Env) (e1 e2 e3 : Exp) (v : Value) (x y : Var),
                    EvalTo E e1 VNil -> EvalTo E e2 v ->
                    EvalTo E (EMatch e1 e2 x y e3) v
    | E_MatchCons : forall (E : Env) (e1 e2 e3 : Exp) (x y : Var)
                           (v v1 v2 : Value),
                    EvalTo E e1 (VCons v1 v2) ->
                    EvalTo (EBind (EBind E x v1) y v2) e3 v ->
                    EvalTo E (EMatch e1 e2 x y e3) v.

End PatternMatching.

