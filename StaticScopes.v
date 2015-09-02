Section StaticScopes.
Require Import Functions.
Require Import ZArith.
Open Scope Z_scope.

(* Variables (reused) *)
Inductive Var : Set :=
    | VId : nat -> Var.

(* Expressions with de Bruijn indices at p.97 and p.100 *)
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

End StaticScopes.

