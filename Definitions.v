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
    | EPlus  : Exp -> Exp -> Exp
    | EMinus : Exp -> Exp -> Exp
    | ETimes : Exp -> Exp -> Exp
    | ELt    : Exp -> Exp -> Exp
    | EIf    : Exp -> Exp -> Exp -> Exp
    | ELet   : Var -> Exp -> Exp -> Exp.

(* Definitions at pp.56-57 *)
Inductive Plus : Z -> Z -> Z -> Prop :=
    | B_Plus : forall i1 i2 i3 : Z, i3 = i1 + i2 -> Plus i1 i2 i3.
Inductive Minus : Z -> Z -> Z -> Prop :=
    | B_Minus : forall i1 i2 i3 : Z, i3 = i1 - i2 -> Minus i1 i2 i3.
Inductive Times : Z -> Z -> Z -> Prop :=
    | B_Times : forall i1 i2 i3 : Z, i3 = i1 * i2 -> Times i1 i2 i3.
Inductive Lt : Z -> Z -> bool -> Prop :=
    | B_Lt : forall (i1 i2 : Z) (b3 : bool), b3 = (i1 <? i2) -> Lt i1 i2 b3.

(* Fig 4.1 *)
Inductive EvalTo : Env -> Exp -> Value -> Prop :=
    | E_Int   : forall (E : Env) (i : Z),
                EvalTo E (EValue (VInt i)) (VInt i)
    | E_Bool  : forall (E : Env) (b : bool),
                EvalTo E (EValue (VBool b)) (VBool b)
    | E_Var1  : forall (E : Env) (x : Var) (v : Value),
                EvalTo (ECons E x v) (EVar x) v
    | E_Var2  : forall (E : Env) (x y : Var) (v1 v2 : Value),
                x <> y -> EvalTo E (EVar x) v2 ->
                EvalTo (ECons E y v1) (EVar x) v2
    | E_Plus  : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                Plus i1 i2 i3 ->
                EvalTo E (EPlus e1 e2) (VInt i3)
    | E_Minus : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                Minus i1 i2 i3 ->
                EvalTo E (EMinus e1 e2) (VInt i3)
    | E_Times : forall (E : Env) (e1 e2 e3 : Exp) (i1 i2 i3 : Z),
                EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                Times i1 i2 i3 ->
                EvalTo E (ETimes e1 e2) (VInt i3)
    | E_Lt    : forall (E : Env) (e1 e2 : Exp) (i1 i2 : Z) (b3 : bool),
                EvalTo E e1 (VInt i1) -> EvalTo E e2 (VInt i2) ->
                Lt i1 i2 b3 ->
                EvalTo E (ELt e1 e2) (VBool b3)
    | E_IfT   : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                EvalTo E e1 (VBool true) -> EvalTo E e2 v ->
                EvalTo E (EIf e1 e2 e3) v
    | E_IfF   : forall (E : Env) (e1 e2 e3 : Exp) (v : Value),
                EvalTo E e1 (VBool false) -> EvalTo E e3 v ->
                EvalTo E (EIf e1 e2 e3) v
    | E_Let   : forall (E : Env) (e1 e2 : Exp) (x : Var) (v1 v : Value),
                EvalTo E e1 v1 -> EvalTo (ECons E x v1) e2 v ->
                EvalTo E (ELet x e1 e2) v.

(* Lemma 4.2 *)
Lemma EvalTo_Var_uniq :
    forall (E : Env) (x : Var) (v v' : Value),
    EvalTo E (EVar x) v -> EvalTo E (EVar x) v' -> v = v'.
Proof.
    induction E as [| E0 H0 x0 v0].

        (* Case : E = ENil *)
        intros x v v' H H'.
        inversion H.

        (* Case : E = ECons E0 x0 v0 *)
        intros x v v' H H'.
        inversion H; subst.

            (* Case : H is from E_Var1 *)
            inversion H'; subst.

                (* Case : H' is from E_Var1 *)
                reflexivity.

                (* Case : H' is from E_Var2 *)
                contradict H6.
                reflexivity.

            (* Case : H' is from E_Var2 *)
            inversion H'; subst.

                (* Case : H' is from E_Var1 *)
                contradict H6.
                reflexivity.

                (* Case : H' is from E_Var2 *)
                apply (H0 _ _ _ H7 H9).
Qed.

End Definitions.

