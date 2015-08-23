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

(* Decidability of Var *)
Lemma Var_eq_dec :
    forall x y : Var, {x = y} + {x <> y}.
Proof.
Admitted.

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

(* Free variables at p.72 *)
Inductive is_FV : Exp -> Var -> Prop :=
    | FV_Var     : forall x : Var, is_FV (EVar x) x
    | FV_Plus_l  : forall (e1 e2 : Exp) (x : Var),
                   is_FV e1 x -> is_FV (EPlus e1 e2) x
    | FV_Plus_r  : forall (e1 e2 : Exp) (x : Var),
                   is_FV e2 x -> is_FV (EPlus e1 e2) x
    | FV_Minus_l : forall (e1 e2 : Exp) (x : Var),
                   is_FV e1 x -> is_FV (EMinus e1 e2) x
    | FV_Minus_r : forall (e1 e2 : Exp) (x : Var),
                   is_FV e2 x -> is_FV (EMinus e1 e2) x
    | FV_Times_l : forall (e1 e2 : Exp) (x : Var),
                   is_FV e1 x -> is_FV (ETimes e1 e2) x
    | FV_Times_r : forall (e1 e2 : Exp) (x : Var),
                   is_FV e2 x -> is_FV (ETimes e1 e2) x
    | FV_Lt_l    : forall (e1 e2 : Exp) (x : Var),
                   is_FV e1 x -> is_FV (ELt e1 e2) x
    | FV_Lt_r    : forall (e1 e2 : Exp) (x : Var),
                   is_FV e2 x -> is_FV (ELt e1 e2) x
    | FV_If      : forall (e1 e2 e3 : Exp) (x : Var),
                   is_FV e1 x -> is_FV (EIf e1 e2 e3) x
    | FV_IfT     : forall (e1 e2 e3 : Exp) (x : Var),
                   is_FV e2 x -> is_FV (EIf e1 e2 e3) x
    | FV_IfF     : forall (e1 e2 e3 : Exp) (x : Var),
                   is_FV e3 x -> is_FV (EIf e1 e2 e3) x
    | FV_Let1    : forall (e1 e2 : Exp) (x y : Var),
                   is_FV e1 x -> is_FV (ELet y e1 e2) x
    | FV_Let2    : forall (e1 e2 : Exp) (x y : Var),
                   is_FV e2 x -> x <> y -> is_FV (ELet y e1 e2) x.

(* Domains at p.73 *)
Inductive in_dom : Env -> Var -> Prop :=
    | Dom_ECons1 : forall (E : Env) (x : Var) (v : Value),
                   in_dom (ECons E x v) x
    | Dom_ECons2 : forall (E : Env) (x y : Var) (v : Value),
                   in_dom E x -> in_dom (ECons E y v) x.

(* Errors at p.75 *)
Inductive Error : Env -> Exp -> Prop :=
    | E_IfInt       : forall (E : Env) (e1 e2 e3 : Exp) (i : Z),
                      EvalTo E e1 (VInt i) -> Error E (EIf e1 e2 e3)
    | E_PlusBoolL   : forall (E : Env) (e1 e2 : Exp) (b : bool),
                      EvalTo E e1 (VBool b) -> Error E (EPlus e1 e2)
    | E_PlusBoolR   : forall (E : Env) (e1 e2 : Exp) (b : bool),
                      EvalTo E e2 (VBool b) -> Error E (EPlus e1 e2)
    | E_MinusBoolL  : forall (E : Env) (e1 e2 : Exp) (b : bool),
                      EvalTo E e1 (VBool b) -> Error E (EMinus e1 e2)
    | E_MinusBoolR  : forall (E : Env) (e1 e2 : Exp) (b : bool),
                      EvalTo E e2 (VBool b) -> Error E (EMinus e1 e2)
    | E_TimesBoolL  : forall (E : Env) (e1 e2 : Exp) (b : bool),
                      EvalTo E e1 (VBool b) -> Error E (ETimes e1 e2)
    | E_TimesBoolR  : forall (E : Env) (e1 e2 : Exp) (b : bool),
                      EvalTo E e2 (VBool b) -> Error E (ETimes e1 e2)
    | E_LtBoolL     : forall (E : Env) (e1 e2 : Exp) (b : bool),
                      EvalTo E e1 (VBool b) -> Error E (ELt e1 e2)
    | E_LtBoolR     : forall (E : Env) (e1 e2 : Exp) (b : bool),
                      EvalTo E e2 (VBool b) -> Error E (ELt e1 e2)
    | E_IfError     : forall (E : Env) (e1 e2 e3 : Exp),
                      Error E e1 -> Error E (EIf e1 e2 e3)
    | E_IfTError    : forall (E : Env) (e1 e2 e3 : Exp),
                      EvalTo E e1 (VBool true) -> Error E e2 ->
                      Error E (EIf e1 e2 e3)
    | E_IfFError    : forall (E : Env) (e1 e2 e3 : Exp),
                      EvalTo E e1 (VBool false) -> Error E e3 ->
                      Error E (EIf e1 e2 e3)
    | E_PlusErrorL  : forall (E : Env) (e1 e2 : Exp),
                      Error E e1 -> Error E (EPlus e1 e2)
    | E_PlusErrorR  : forall (E : Env) (e1 e2 : Exp),
                      Error E e2 -> Error E (EPlus e1 e2)
    | E_MinusErrorL : forall (E : Env) (e1 e2 : Exp),
                      Error E e1 -> Error E (EMinus e1 e2)
    | E_MinusErrorR : forall (E : Env) (e1 e2 : Exp),
                      Error E e2 -> Error E (EMinus e1 e2)
    | E_TimesErrorL : forall (E : Env) (e1 e2 : Exp),
                      Error E e1 -> Error E (ETimes e1 e2)
    | E_TimesErrorR : forall (E : Env) (e1 e2 : Exp),
                      Error E e2 -> Error E (ETimes e1 e2)
    | E_LtErrorL    : forall (E : Env) (e1 e2 : Exp),
                      Error E e1 -> Error E (ELt e1 e2)
    | E_LtErrorR    : forall (E : Env) (e1 e2 : Exp),
                      Error E e2 -> Error E (ELt e1 e2)
    | E_LetError1   : forall (E : Env) (x : Var) (e1 e2 : Exp),
                      Error E e1 -> Error E (ELet x e1 e2)
    | E_LetError2   : forall (E : Env) (x : Var) (v : Value) (e1 e2 : Exp),
                      EvalTo E e1 v -> Error (ECons E x v) e2 ->
                      Error E (ELet x e1 e2).

(* Theorem 4.3 *)
Theorem EvalTo_Error_total :
    forall (E : Env) (e : Exp),
    (forall x : Var, is_FV e x -> in_dom E x) ->
    (exists v : Value, EvalTo E e v) \/ Error E e.
Proof.
    intros E e H.
    induction e as [[i | b] | x | e1 He1 e2 He2 | | | | |].

        (* Case : e = VInt i *)
        left.
        exists (VInt i).
        apply E_Int.

        (* Case : e = VBool b *)
        left.
        exists (VBool b).
        apply E_Bool.

        (* Case : e = EVar x *)
        specialize (H x (FV_Var _)).
        induction H as [E0 x v | E0 x y v H0 H].

            (* Case : E = ECons E0 x v *)
            left.
            exists v.
            apply E_Var1.

            (* Case : in_dom E0 x *)
            destruct (Var_eq_dec x y) as [D | D].

                (* Case : x = y *)
                subst.
                left.
                exists v.
                apply E_Var1.

                (* Case : x <> y *)
                destruct H as [[v' H] | H].

                    (* Case : EvalTo E0 (EVar x) v' *)
                    left.
                    exists v'.
                    apply (E_Var2 E0 _ _ _ _ D H).

                    (* Case : Error E0 (EVar x) *)
                    inversion H.

        (* Case : e = EPlus e1 e2 *)
        assert (forall x : Var, is_FV e1 x -> in_dom E x) as HFV1.

            (* Proof of the assertion *)
            intros x Hx.
            apply H.
            apply (FV_Plus_l _ _ _ Hx).

        assert (forall x : Var, is_FV e2 x -> in_dom E x) as HFV2.

            (* Proof of the assertion *)
            intros x Hx.
            apply H.
            apply (FV_Plus_r _ _ _ Hx).

        specialize (He1 HFV1); clear HFV1.
        specialize (He2 HFV2); clear HFV2.
        destruct He1 as [[[i1 | b1] He1] | He1].

            (* Case : EvalTo E e1 (VInt i1) *)
            destruct He2 as [[[i2 | b2] He2] | He2].

                (* Case : EvalTo E e2 (VInt i2) *)
                left.
                exists (VInt (i1 + i2)).
                apply (E_Plus _ _ _ (EValue (VInt (i1 + i2))) _ _ _ He1 He2).
                apply B_Plus.
                reflexivity.

                (* Case : EvalTo E e2 (VBool b2) *)
                right.
                apply (E_PlusBoolR _ _ _ _ He2).

                (* Case : Error E e2 *)
                right.
                apply (E_PlusErrorR _ _ _ He2).

            (* Case : EvalTo E e1 (VBool b1) *)
            right.
            apply (E_PlusBoolL _ _ _ _ He1).

            (* Case : Error E e1 *)
            right.
            apply (E_PlusErrorL _ _ _ He1).
Admitted.

End Definitions.

