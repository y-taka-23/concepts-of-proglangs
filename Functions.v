Section Functions.
Require Import ZArith.
Open Scope Z_scope.

(* Variables (reused) *)
Inductive Var : Set :=
    | VId : nat -> Var.

(* Expressions at p.84 and p.87 *)
Inductive Exp : Set :=
    | EValue  : Value -> Exp
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
    with Value : Set :=
    | VInt    : Z -> Value
    | VBool   : bool -> Value
    | VFun    : Env -> Var -> Exp -> Value
    | VRecFun : Env -> Var -> Var -> Exp -> Value
    with Env : Set :=
    | ENil  : Env
    | ECons : Env -> Var -> Value -> Env.

(* Definitions at pp.56-57 (reused) *)
Inductive Plus : Z -> Z -> Z -> Prop :=
    | B_Plus : forall i1 i2 i3 : Z, i3 = i1 + i2 -> Plus i1 i2 i3.
Inductive Minus : Z -> Z -> Z -> Prop :=
    | B_Minus : forall i1 i2 i3 : Z, i3 = i1 - i2 -> Minus i1 i2 i3.
Inductive Times : Z -> Z -> Z -> Prop :=
    | B_Times : forall i1 i2 i3 : Z, i3 = i1 * i2 -> Times i1 i2 i3.
Inductive Lt : Z -> Z -> bool -> Prop :=
    | B_Lt : forall (i1 i2 : Z) (b3 : bool), b3 = (i1 <? i2) -> Lt i1 i2 b3.

(* Evaluations at p.84 and p.87 *)
Inductive EvalTo : Env -> Exp -> Value -> Prop :=
    | E_Int    : forall (E : Env) (i : Z),
                 EvalTo E (EValue (VInt i)) (VInt i)
    | E_Bool   : forall (E : Env) (b : bool),
                 EvalTo E (EValue (VBool b)) (VBool b)
    | E_Var1   : forall (E : Env) (x : Var) (v : Value),
                 EvalTo (ECons E x v) (EVar x) v
    | E_Var2   : forall (E : Env) (x y : Var) (v1 v2 : Value),
                 x <> y -> EvalTo E (EVar x) v2 ->
                 EvalTo (ECons E y v1) (EVar x) v2
    | E_Plus   : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                 EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                 Plus i1 i2 i3 ->
                 EvalTo E (EPlus e1 e2) (VInt i3)
    | E_Minus  : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                 EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                 Minus i1 i2 i3 ->
                 EvalTo E (EMinus e1 e2) (VInt i3)
    | E_Times  : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                 EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                 Times i1 i2 i3 ->
                 EvalTo E (ETimes e1 e2) (VInt i3)
    | E_Lt     : forall (E : Env) (e1 e2 : Exp) (i1 i2 : Z) (b3 : bool),
                 EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                 Lt i1 i2 b3 ->
                 EvalTo E (ELt e1 e2) (VBool b3)
    | E_IfT    : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                 EvalTo E e1 (VBool true) -> EvalTo E e2 v ->
                 EvalTo E (EIf e1 e2 e3) v
    | E_IfF    : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                 EvalTo E e1 (VBool false) -> EvalTo E e3 v ->
                 EvalTo E (EIf e1 e2 e3) v
    | E_Let    : forall (E : Env) (e1 e2 : Exp) (x : Var) (v1 v : Value),
                 EvalTo E e1 v1 -> EvalTo (ECons E x v1) e2 v ->
                 EvalTo E (ELet x e1 e2) v
    | E_Fun    : forall (E : Env) (x : Var) (e : Exp),
                 EvalTo E (EFun x e) (VFun E x e)
    | E_App    : forall (E E2 : Env) (e1 e2 e0 : Exp) (x : Var) (v v2 : Value),
                 EvalTo E e1 (VFun E2 x e0) -> EvalTo E e2 v2 ->
                 EvalTo (ECons E2 x v2) e0 v ->
                 EvalTo E (EApp e1 e2) v
    | E_LetRec : forall (E : Env) (x y : Var) (e1 e2 : Exp) (v : Value),
                 EvalTo (ECons E x (VRecFun E x y e1)) e2 v ->
                 EvalTo E (ELetRec x y e1 e2) v
    | E_AppRec : forall (E E2 : Env) (e1 e2 e0 : Exp) (x y : Var)
                        (v v2 : Value),
                 EvalTo E e1 (VRecFun E2 x y e0) -> EvalTo E e2 v2 ->
                 EvalTo (ECons (ECons E2 x (VRecFun E2 x y e2)) y v2) e0 v ->
                 EvalTo E (EApp e1 e2) v.

End Functions.

