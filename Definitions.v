Section Definitions.
Require Import ZArith.
Open Scope Z_scope.

(* Values (reused) *)
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

(* Definitions at pp.56-57 (reused) *)
Inductive Plus : Z -> Z -> Z -> Prop :=
    | B_Plus : forall i1 i2 i3 : Z, i3 = i1 + i2 -> Plus i1 i2 i3.
Inductive Minus : Z -> Z -> Z -> Prop :=
    | B_Minus : forall i1 i2 i3 : Z, i3 = i1 - i2 -> Minus i1 i2 i3.
Inductive Times : Z -> Z -> Z -> Prop :=
    | B_Times : forall i1 i2 i3 : Z, i3 = i1 * i2 -> Times i1 i2 i3.
Inductive Lt : Z -> Z -> bool -> Prop :=
    | B_Lt : forall (i1 i2 : Z) (b3 : bool), b3 = (i1 <? i2) -> Lt i1 i2 b3.

Lemma Plus_uniq :
    forall i1 i2 i3 i4 : Z, Plus i1 i2 i3 -> Plus i1 i2 i4 -> i3 = i4.
Proof.
    intros i1 i2 i3 i4 H3 H4.
    inversion H3; subst.
    inversion H4; subst.
    reflexivity.
Qed.

Lemma Minus_uniq :
    forall i1 i2 i3 i4 : Z, Minus i1 i2 i3 -> Minus i1 i2 i4 -> i3 = i4.
Proof.
    intros i1 i2 i3 i4 H3 H4.
    inversion H3; subst.
    inversion H4; subst.
    reflexivity.
Qed.

Lemma Times_uniq :
    forall i1 i2 i3 i4 : Z, Times i1 i2 i3 -> Times i1 i2 i4 -> i3 = i4.
Proof.
    intros i1 i2 i3 i4 H3 H4.
    inversion H3; subst.
    inversion H4; subst.
    reflexivity.
Qed.

Lemma Lt_uniq :
    forall (i1 i2 : Z) (b1 b2 : bool), Lt i1 i2 b1 -> Lt i1 i2 b2 -> b1 = b2.
Proof.
    intros i1 i2 i3 i4 H3 H4.
    inversion H3; subst.
    inversion H4; subst.
    reflexivity.
Qed.

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

(* Theorem 4.1 *)
Theorem EvalTo_uniq :
    forall (E : Env) (e : Exp) (v v' : Value),
    EvalTo E e v -> EvalTo E e v' -> v = v'.
Proof.
    intros E e.
    generalize dependent E.
    induction e as [[i | b] | x |
                    e1 He1 e2 He2 | e1 He1 e2 He2 | e1 He1 e2 He2 |
                    e1 He1 e2 He2 | e1 He1 e2 He2 e3 He3 | x e1 He1 e2 He2 ].

        (* Case : e = VInt i *)
        intros E v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        reflexivity.

        (* Case : e = VBool b *)
        intros E v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        reflexivity.

        (* Case : e = EVar x *)
        intros E v1 v2 H1 H2.
        apply (EvalTo_Var_uniq _ _ _ _ H1 H2).

        (* Case : e = EPlus e1 e2 *)
        intros E v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        assert (VInt i1 = VInt i0) as Hi1 by apply (He1 _ _ _ H3 H4).
        inversion Hi1; subst; clear Hi1.
        assert (VInt i2 = VInt i4) as Hi2 by apply (He2 _ _ _ H5 H8).
        inversion Hi2; subst; clear Hi2.
        assert (i3 = i5) by apply (Plus_uniq _ _ _ _ H7 H10); subst.
        reflexivity.

        (* Case : e = EMinus e1 e2 *)
        intros E v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        assert (VInt i1 = VInt i0) as Hi1 by apply (He1 _ _ _ H3 H4).
        inversion Hi1; subst; clear Hi1.
        assert (VInt i2 = VInt i4) as Hi2 by apply (He2 _ _ _ H5 H8).
        inversion Hi2; subst; clear Hi2.
        assert (i3 = i5) by apply (Minus_uniq _ _ _ _ H7 H10); subst.
        reflexivity.

        (* Case : e = ETimes e1 e2 *)
        intros E v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        assert (VInt i1 = VInt i0) as Hi1 by apply (He1 _ _ _ H3 H4).
        inversion Hi1; subst; clear Hi1.
        assert (VInt i2 = VInt i4) as Hi2 by apply (He2 _ _ _ H5 H8).
        inversion Hi2; subst; clear Hi2.
        assert (i3 = i5) by apply (Times_uniq _ _ _ _ H7 H10); subst.
        reflexivity.

        (* Case : e = ELt e1 e2 *)
        intros E v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        assert (VInt i1 = VInt i0) as Hi1 by apply (He1 _ _ _ H3 H4).
        inversion Hi1; subst; clear Hi1.
        assert (VInt i2 = VInt i3) as Hi2 by apply (He2 _ _ _ H5 H8).
        inversion Hi2; subst; clear Hi2.
        assert (b3 = b0) by apply (Lt_uniq _ _ _ _ H7 H10); subst.
        reflexivity.

        (* Case : e = EIf e1 e2 e3 *)
        intros E v1 v2 H1 H2.
        inversion H1; subst.

            (* Case : EvalTo e1 (VBool true) *)
            inversion H2; subst.

                (* Case : EvalTo e2 (VBool true) *)
                apply (He2 _ _ _ H7 H9).

                (* Case : EvalTo e2 (VBool false) *)
                discriminate (He1 _ _ _ H6 H8).

            (* Case : EvalTo e1 (VBool false) *)
            inversion H2; subst.

                (* Case : EvalTo e2 (VBool true) *)
                discriminate (He1 _ _ _ H6 H8).

                (* Case : EvalTo e2 (VBool false) *)
                apply (He3 _ _ _ H7 H9).

        (* Case : e = ELet x e1 e2 *)
        intros E v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        assert (v0 = v3) by apply (He1 _ _ _ H6 H8) ; subst.
        apply (He2 _ _ _ H7 H9).
Qed.

End Definitions.

