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
    | DBVRecFun : DBValueList -> DBValue
    with DBValueList : Set :=
    | DVBLNil  : DBValueList
    | DVBLCons : DBValueList -> DBValue -> DBValueList.

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

End StaticScopes.

