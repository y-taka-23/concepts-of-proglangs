Section Definitions.
Require Import ZArith.
Open Scope Z_scope.

(* v in Value ::= i | b (in def 3.1) *)
Inductive Value : Set := 
    | VInt  : Z -> Value
    | VBool : bool -> Value.

(* Variables at p.71 *)
Inductive Var : Set :=
    | VId : nat -> Var.

(* Environments at p.71 *)
Inductive Env : Set :=
    | ENil  : Env 
    | ECons : Env -> Var -> Value -> Env.

(* Definition at p.71 *)
Inductive Exp : Set :=
    | EValue : Value -> Exp
    | EVar   : Var -> Exp
    | ELet   : Var -> Exp -> Exp -> Exp
    | EIf    : Exp -> Exp -> Exp -> Exp
    | EPlus  : Exp -> Exp -> Exp
    | EMinus : Exp -> Exp -> Exp
    | ETimes : Exp -> Exp -> Exp
    | ELt    : Exp -> Exp -> Exp.

End Definitions.

