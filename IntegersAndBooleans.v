Section IntegersAndBooleans.
Require Import ZArith.
Open Scope Z_scope.

(* v in Value ::= i | b (in def 3.1) *)
Inductive Value : Set := 
    | VInt  : Z -> Value
    | VBool : bool -> Value.

(* Def 3.1 *)
Inductive Exp : Set :=
    | EValue : Value -> Exp
    | EIf    : Exp -> Exp -> Exp -> Exp
    | EPlus  : Exp -> Exp -> Exp
    | EMinus : Exp -> Exp -> Exp
    | ETimes : Exp -> Exp -> Exp
    | ELt    : Exp -> Exp -> Exp.

(* Definitions at pp.56-57 *)
Inductive Plus : Z -> Z -> Z -> Prop :=
    | B_Plus : forall i1 i2 i3 : Z, i3 = i1 + i2 -> Plus i1 i2 i3.
Inductive Minus : Z -> Z -> Z -> Prop :=
    | B_Minus : forall i1 i2 i3 : Z, i3 = i1 - i2 -> Minus i1 i2 i3.
Inductive Times : Z -> Z -> Z -> Prop :=
    | B_Times : forall i1 i2 i3 : Z, i3 = i1 * i2 -> Times i1 i2 i3.
Inductive Lt : Z -> Z -> bool -> Prop := 
    | B_Lt : forall (i1 i2 : Z) (b3 : bool), b3 = (i1 <? i2) -> Lt i1 i2 b3.

(* Definition at p.56 *)
Inductive EvalTo : Exp -> Value -> Prop :=
    | E_Int   : forall i : Z, EvalTo (EValue (VInt i)) (VInt i)
    | E_Bool  : forall b : bool, EvalTo (EValue (VBool b)) (VBool b)
    | E_IfT   : forall (e1 e2 e3 : Exp) (v : Value),
                EvalTo e1 (VBool true) -> EvalTo e2 v ->
                EvalTo (EIf e1 e2 e3) v
    | E_IfF   : forall (e1 e2 e3 : Exp) (v : Value),
                EvalTo e1 (VBool false) -> EvalTo e3 v ->
                EvalTo (EIf e1 e2 e3) v
    | E_Plus  : forall (e1 e2 : Exp) (i1 i2 i3 : Z),
                EvalTo e1 (VInt i1) -> EvalTo e2 (VInt i2) -> Plus i1 i2 i3 ->
                EvalTo (EPlus e1 e2) (VInt i3)
    | E_Minus : forall (e1 e2 : Exp) (i1 i2 i3 : Z),
                EvalTo e1 (VInt i1) -> EvalTo e2 (VInt i2) -> Minus i1 i2 i3 ->
                EvalTo (EMinus e1 e2) (VInt i3)
    | E_Times : forall (e1 e2 : Exp) (i1 i2 i3 : Z),
                EvalTo e1 (VInt i1) -> EvalTo e2 (VInt i2) -> Times i1 i2 i3 ->
                EvalTo (ETimes e1 e2) (VInt i3)
    | E_Lt    : forall (e1 e2 : Exp) (i1 i2 : Z) (b3 : bool),
                EvalTo e1 (VInt i1) -> EvalTo e2 (VInt i2) -> Lt i1 i2 b3 ->
                EvalTo (ELt e1 e2) (VBool b3).

(* Theorem 3.2 *)
Theorem EvalTo_uniq :
    forall (e : Exp) (v1 v2 : Value), EvalTo e v1 -> EvalTo e v2 -> v1 = v2.
Proof.
Admitted.

End IntegersAndBooleans.

