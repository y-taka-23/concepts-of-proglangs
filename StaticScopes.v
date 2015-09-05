Section StaticScopes.
Require Import Functions.
Require Import ZArith.
Open Scope Z_scope.

(* Expressions with de Bruijn indices at p.97 and p.100 *)
(* The indices are 0-besed, unlike the definition in the text *)
Inductive DBExp : Set :=
    | DBEValue  : DBValue -> DBExp
    | DBEVar    : nat -> DBExp
    | DBEPlus   : DBExp -> DBExp -> DBExp
    | DBEMinus  : DBExp -> DBExp -> DBExp
    | DBETimes  : DBExp -> DBExp -> DBExp
    | DBELt     : DBExp -> DBExp -> DBExp
    | DBEIf     : DBExp -> DBExp -> DBExp -> DBExp
    | DBELet    : DBExp -> DBExp -> DBExp
    | DBEFun    : DBExp -> DBExp
    | DBEApp    : DBExp -> DBExp -> DBExp
    | DBELetRec : DBExp -> DBExp -> DBExp
    with DBValue : Set :=
    | DBVInt    : Z -> DBValue
    | DBVBool   : bool -> DBValue
    | DBVFun    : DBValueList -> DBExp -> DBValue
    | DBVRecFun : DBValueList -> DBExp -> DBValue
    with DBValueList : Set :=
    | DBVLNil  : DBValueList
    | DBVLCons : DBValueList -> DBValue -> DBValueList.

(* Variable list at p.97 *)
Inductive VarList : Set :=
    | VLNil  : VarList
    | VLCons : VarList -> Var -> VarList.

(* Fig 6.1, 6.2 *)
Inductive TransTo : VarList -> Exp -> DBExp -> Prop :=
    | Tr_Int    : forall (X : VarList) (i : Z),
                  TransTo X (EValue (VInt i)) (DBEValue (DBVInt i))
    | Tr_Bool   : forall (X : VarList) (b : bool),
                  TransTo X (EValue (VBool b)) (DBEValue (DBVBool b))
    | Tr_If     : forall (X : VarList) (e1 e2 e3 : Exp) (d1 d2 d3 : DBExp),
                  TransTo X e1 d1 -> TransTo X e2 d2 -> TransTo X e3 d3 ->
                  TransTo X (EIf e1 e2 e3) (DBEIf d1 d2 d3)
    | Tr_Plus   : forall (X : VarList) (e1 e2 : Exp) (d1 d2 : DBExp),
                  TransTo X e1 d1 -> TransTo X e2 d2 ->
                  TransTo X (EPlus e1 e2) (DBEPlus d1 d2)
    | Tr_Minus  : forall (X : VarList) (e1 e2 : Exp) (d1 d2 : DBExp),
                  TransTo X e1 d1 -> TransTo X e2 d2 ->
                  TransTo X (EMinus e1 e2) (DBEMinus d1 d2)
    | Tr_Times  : forall (X : VarList) (e1 e2 : Exp) (d1 d2 : DBExp),
                  TransTo X e1 d1 -> TransTo X e2 d2 ->
                  TransTo X (ETimes e1 e2) (DBETimes d1 d2)
    | Tr_Lt     : forall (X : VarList) (e1 e2 : Exp) (d1 d2 : DBExp),
                  TransTo X e1 d1 -> TransTo X e2 d2 ->
                  TransTo X (ELt e1 e2) (DBELt d1 d2)
    | Tr_Var1   : forall (X : VarList) (x : Var),
                  TransTo (VLCons X x) (EVar x) (DBEVar O)
    | Tr_Var2   : forall (X : VarList) (x y : Var) (n1 : nat),
                  y <> x -> TransTo X (EVar x) (DBEVar n1) ->
                  TransTo (VLCons X y) (EVar x) (DBEVar (S n1))
    | Tr_Let    : forall (X : VarList) (x : Var) (e1 e2 : Exp) (d1 d2 : DBExp),
                  TransTo X (ELet x e1 e2) (DBELet d1 d2)
    | Tr_Fun    : forall (X : VarList) (x : Var) (e : Exp) (d : DBExp),
                  TransTo X (EFun x e) (DBEFun d)
    | Tr_App    : forall (X : VarList) (e1 e2 : Exp) (d1 d2 : DBExp),
                  TransTo X e1 d1 -> TransTo X e2 d2 ->
                  TransTo X (EApp e1 e2) (DBEApp d1 d2)
    | Tr_LetRec : forall (X : VarList) (x y : Var)
                         (e1 e2 : Exp) (d1 d2 : DBExp),
                  TransTo (VLCons (VLCons X x) y) e1 d1 ->
                  TransTo (VLCons X x) e2 d2 ->
                  TransTo X (ELetRec x y e1 e2) (DBELetRec d1 d2).

(* V[n] = w of at p.100 *)
Inductive nth_val : DBValueList -> nat -> DBValue -> Prop :=
    | NV_O : forall w : DBValue, nth_val (DBVLCons DBVLNil w) O w
    | NV_S : forall (V : DBValueList) (n : nat) (w w0 : DBValue),
             nth_val V n w ->
             nth_val (DBVLCons V w0) (S n) w.

(* Fig 6.3, 6.4 *)
Inductive DBEvalTo : DBValueList -> DBExp -> DBValue -> Prop :=
    | DBE_Int    : forall (V : DBValueList) (i : Z),
                   DBEvalTo V (DBEValue (DBVInt i)) (DBVInt i)
    | DBE_Bool   : forall (V : DBValueList) (b : bool),
                   DBEvalTo V (DBEValue (DBVBool b)) (DBVBool b)
    | DBE_IfT    : forall (V : DBValueList) (d1 d2 d3 : DBExp) (w : DBValue),
                   DBEvalTo V d1 (DBVBool true) -> DBEvalTo V d2 w ->
                   DBEvalTo V (DBEIf d1 d2 d3) w
    | DBE_IfF    : forall (V : DBValueList) (d1 d2 d3 : DBExp) (w : DBValue),
                   DBEvalTo V d1 (DBVBool false) -> DBEvalTo V d3 w ->
                   DBEvalTo V (DBEIf d1 d2 d3) w
    | DBE_Plus   : forall (V : DBValueList) (d1 d2 d3 : DBExp) (i1 i2 i3 : Z),
                   DBEvalTo V d1 (DBVInt i1) -> DBEvalTo V d2 (DBVInt i2) ->
                   Plus i1 i2 i3 ->
                   DBEvalTo V (DBEPlus d1 d2) (DBVInt i3)
    | DBE_Minus  : forall (V : DBValueList) (d1 d2 d3 : DBExp) (i1 i2 i3 : Z),
                   DBEvalTo V d1 (DBVInt i1) -> DBEvalTo V d2 (DBVInt i2) ->
                   Minus i1 i2 i3 ->
                   DBEvalTo V (DBEMinus d1 d2) (DBVInt i3)
    | DBE_Times  : forall (V : DBValueList) (d1 d2 d3 : DBExp) (i1 i2 i3 : Z),
                   DBEvalTo V d1 (DBVInt i1) -> DBEvalTo V d2 (DBVInt i2) ->
                   Times i1 i2 i3 ->
                   DBEvalTo V (DBETimes d1 d2) (DBVInt i3)
    | DBE_Lt     : forall (V : DBValueList) (d1 d2 d3 : DBExp)
                          (i1 i2 : Z) (b3 : bool),
                   DBEvalTo V d1 (DBVInt i1) -> DBEvalTo V d2 (DBVInt i2) ->
                   Lt i1 i2 b3 ->
                   DBEvalTo V (DBELt d1 d2) (DBVBool b3)
    | DBE_Var    : forall (V : DBValueList) (n : nat) (w : DBValue),
                   nth_val V n w ->
                   DBEvalTo V (DBEVar n) w
    | DBE_Let    : forall (V : DBValueList) (d1 d2 : DBExp) (w w1 : DBValue),
                   DBEvalTo V d1 w1 -> DBEvalTo (DBVLCons V w1) d2 w ->
                   DBEvalTo V (DBELet d1 d2) w
    | DBE_Fun    : forall (V : DBValueList) (d : DBExp),
                   DBEvalTo V (DBEFun d) (DBVFun V d)
    | DBE_App    : forall (V V2 : DBValueList) (d1 d2 d0 : DBExp)
                          (w w2 : DBValue),
                   DBEvalTo V d1 (DBVFun V2 d0) -> DBEvalTo V d2 w2 ->
                   DBEvalTo (DBVLCons V2 w2) d0 w ->
                   DBEvalTo V (DBEApp d1 d2) w
    | DBE_LetRec : forall (V : DBValueList) (d1 d2 : DBExp) (w : DBValue),
                   DBEvalTo (DBVLCons V (DBVRecFun V d1)) d2 w ->
                   DBEvalTo V (DBELetRec d1 d2) w
    | DBE_AppRec : forall (V V2 : DBValueList) (d1 d2 d0 : DBExp)
                          (w w2 : DBValue),
                   DBEvalTo V d2 (DBVRecFun V2 d0) -> DBEvalTo V d2 w2 ->
                   DBEvalTo (DBVLCons (DBVLCons V2 (DBVRecFun V2 d0)) w2) d0 w ->
                   DBEvalTo V (DBEApp d1 d2) w.

(* Fig 6.5 *)
Inductive TransValTo : Value -> DBValue -> Prop :=
    | Trv_Int  : forall i : Z, TransValTo (VInt i) (DBVInt i)
    | Trv_Bool : forall b : bool, TransValTo (VBool b) (DBVBool b)
    | Trv_Fun  : forall (E : Env) (X : VarList) (V : DBValueList) (x : Var)
                        (e : Exp) (d : DBExp),
                 TransEnvTo E X V -> TransTo (VLCons X x) e d ->
                 TransValTo (VFun E x e) (DBVFun V d)
    | Trv_Rec  : forall (E : Env) (X : VarList) (V : DBValueList) (x y : Var)
                        (e : Exp) (d : DBExp),
                 TransEnvTo E X V -> TransTo (VLCons (VLCons X x) y) e d ->
                 TransValTo (VRecFun E x y e) (DBVRecFun V d)
    with TransEnvTo : Env -> VarList -> DBValueList -> Prop :=
    | Tre_Empty : TransEnvTo ENil VLNil DBVLNil
    | Tre_Bind  : forall (E : Env) (X : VarList) (V : DBValueList)
                         (x : Var) (v : Value) (w : DBValue),
                  TransEnvTo E X V -> TransValTo v w ->
                  TransEnvTo (ECons E x v) (VLCons X x) (DBVLCons V w).

(* Theorem 6.1 (1) *)
Theorem EvalTo_DBEvalTo_compat :
    forall (E : Env) (X : VarList) (V : DBValueList)
           (e : Exp) (d : DBExp) (v : Value),
    TransEnvTo E X V -> TransTo X e d -> EvalTo E e v ->
    exists w : DBValue, (DBEvalTo V d w /\ TransValTo v w).
Proof.
Admitted.

(* Theorem 6.1 (2) *)
Theorem DBEvalTo_EvalTo_compat :
    forall (E : Env) (X : VarList) (V : DBValueList)
           (e : Exp) (d : DBExp) (w : DBValue),
    TransEnvTo E X V -> TransTo X e d -> DBEvalTo V d w ->
    exists v : Value, (EvalTo E e v /\ TransValTo v w).
Proof.
Admitted.

End StaticScopes.

