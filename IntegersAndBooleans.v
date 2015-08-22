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
    induction e as [ v | e1 He1 e2 He2 e3 He3 |
                    e1 He1 e2 He2 | e1 He1 e2 He2 | e1 He1 e2 He2 |
                    e1 He1 e2 He2 ].

        (* Case : e = EValue v *)
        intros v1 v2 H1 H2.
        inversion H1; subst.

            (* Case : v1 = VInt i *)
            inversion H2; subst.
            reflexivity.

            (* Case : v1 = VBool b *)
            inversion H2; subst.
            reflexivity.

        (* Case : f = EIf e1 e2 e3 *)
        intros v1 v2 H1 H2.
        inversion H1; subst.

            (* Case : v1 = VBool true *)
            inversion H2; subst.

                (* Case : v2 = VBool true *)
                apply (He2 _ _ H6 H8).

                (* Case : v2 = VBool true *)
                discriminate (He1 _ _ H5 H7).

            (* Case : v1 = VBool false *)
            inversion H2; subst.

                (* Case : v2 = VBool true *)
                discriminate (He1 _ _ H5 H7).

                (* Case : v2 = VBool false *)
                apply (He3 _ _ H6 H8).

        (* Case : f1 = EPlus e1 e2 *)
        intros v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        assert (VInt i1 = VInt i0) as Hi1 by apply (He1 _ _ H3 H5).
        inversion Hi1; subst; clear Hi1.
        assert (VInt i2 = VInt i4) as Hi2 by apply (He2 _ _ H4 H7).
        inversion Hi2; subst; clear Hi2.
        assert (i3 = i5) by apply (Plus_uniq _ _ _ _ H6 H9); subst.
        reflexivity.

        (* Case : f1 = EMinus e1 e2 *)
        intros v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        assert (VInt i1 = VInt i0) as Hi1 by apply (He1 _ _ H3 H5).
        inversion Hi1; subst; clear Hi1.
        assert (VInt i2 = VInt i4) as Hi2 by apply (He2 _ _ H4 H7).
        inversion Hi2; subst; clear Hi2.
        assert (i3 = i5) by apply (Minus_uniq _ _ _ _ H6 H9); subst.
        reflexivity.

        (* Case : f1 = ETimes e1 e2 *)
        intros v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        assert (VInt i1 = VInt i0) as Hi1 by apply (He1 _ _ H3 H5).
        inversion Hi1; subst; clear Hi1.
        assert (VInt i2 = VInt i4) as Hi2 by apply (He2 _ _ H4 H7).
        inversion Hi2; subst; clear Hi2.
        assert (i3 = i5) by apply (Times_uniq _ _ _ _ H6 H9); subst.
        reflexivity.

        (* Case : f1 = ELt e1 e2 *)
        intros v1 v2 H1 H2.
        inversion H1; subst.
        inversion H2; subst.
        assert (VInt i1 = VInt i0) as Hi1 by apply (He1 _ _ H3 H5).
        inversion Hi1; subst; clear Hi1.
        assert (VInt i2 = VInt i3) as Hi2 by apply (He2 _ _ H4 H7).
        inversion Hi2; subst; clear Hi2.
        assert (b3 = b0) by apply (Lt_uniq _ _ _ _ H6 H9); subst.
        reflexivity.
Qed.

(* Fig. 3.1 and 3.2 *)
Inductive Error : Exp -> Prop :=
    | E_IfInt       : forall (e1 e2 e3 : Exp) (i : Z),
                      EvalTo e1 (VInt i) -> Error (EIf e1 e2 e3)
    | E_PlusBoolL   : forall (e1 e2 : Exp) (b : bool),
                      EvalTo e1 (VBool b) -> Error (EPlus e1 e2)
    | E_PlusBoolR   : forall (e1 e2 : Exp) (b : bool),
                      EvalTo e2 (VBool b) -> Error (EPlus e1 e2)
    | E_MinusBoolL  : forall (e1 e2 : Exp) (b : bool),
                      EvalTo e1 (VBool b) -> Error (EMinus e1 e2)
    | E_MinusBoolR  : forall (e1 e2 : Exp) (b : bool),
                      EvalTo e2 (VBool b) -> Error (EMinus e1 e2)
    | E_TimesBoolL  : forall (e1 e2 : Exp) (b : bool),
                      EvalTo e1 (VBool b) -> Error (ETimes e1 e2)
    | E_TimesBoolR  : forall (e1 e2 : Exp) (b : bool),
                      EvalTo e2 (VBool b) -> Error (ETimes e1 e2)
    | E_LtBoolL     : forall (e1 e2 : Exp) (b : bool),
                      EvalTo e1 (VBool b) -> Error (ELt e1 e2)
    | E_LtBoolR     : forall (e1 e2 : Exp) (b : bool),
                      EvalTo e2 (VBool b) -> Error (ELt e1 e2)
    | E_IfError     : forall e1 e2 e3 : Exp,
                      Error e1 -> Error (EIf e1 e2 e3)
    | E_IfTError    : forall e1 e2 e3 : Exp,
                      EvalTo e1 (VBool true) -> Error e2 ->
                      Error (EIf e1 e2 e3)
    | E_IfFError    : forall e1 e2 e3 : Exp,
                      EvalTo e1 (VBool false) -> Error e3 ->
                      Error (EIf e1 e2 e3)
    | E_PlusErrorL  : forall e1 e2 : Exp, Error e1 -> Error (EPlus e1 e2)
    | E_PlusErrorR  : forall e1 e2 : Exp, Error e2 -> Error (EPlus e1 e2)
    | E_MinusErrorL : forall e1 e2 : Exp, Error e1 -> Error (EMinus e1 e2)
    | E_MinusErrorR : forall e1 e2 : Exp, Error e2 -> Error (EMinus e1 e2)
    | E_TimesErrorL : forall e1 e2 : Exp, Error e1 -> Error (ETimes e1 e2)
    | E_TimesErrorR : forall e1 e2 : Exp, Error e2 -> Error (ETimes e1 e2)
    | E_LtErrorL    : forall e1 e2 : Exp, Error e1 -> Error (ELt e1 e2)
    | E_LtErrorR    : forall e1 e2 : Exp, Error e2 -> Error (ELt e1 e2).

(* Theorem 3.4 *)
Theorem EvalTo_Error_total :
    forall e : Exp, (exists v : Value, EvalTo e v) \/ Error e.
Proof.
    induction e as [ v | e1 He1 e2 He2 e3 He3 |
                    e1 He1 e2 He2 | e1 He1 e2 He2 | e1 He1 e2 He2 |
                    e1 He1 e2 He2 ].

        (* Case : f = EValue v *)
        left.
        exists v.
        induction v as [i | b].

            (* Case : v = VInt i *)
            apply E_Int.

            (* Case : v = VBool b *)
            apply E_Bool.

        (* Case : f = EIf e1 e2 e3 *)
        destruct He1 as [[[i | [|]] He1] | He1].

            (* Case : EvalTo e1 (VInt i) *)
            right.
            apply (E_IfInt _ _ _ _ He1).

            (* Case : EvalTo e1 (VBool true) *)
            destruct He2 as [[v He2] | He2].

                (* Case : EvalTo e2 v *)
                left.
                exists v.
                apply (E_IfT _ _ _ _ He1 He2).

                (* Case : Error e2 *)
                right.
                apply (E_IfTError _ _ _ He1 He2).

            (* Case : EvalTo e1 (VBool false) *)
            destruct He3 as [[v He3] | He3].

                (* Case : EvalTo e3 v *)
                left.
                exists v.
                apply (E_IfF _ _ _ _ He1 He3).

                (* Case : Error e3 *)
                right.
                apply (E_IfFError _ _ _ He1 He3).

            (* Case : Error e1 *)
            right.
            apply (E_IfError _ _ _ He1).

        (* Case : f = EPlus e1 e2 *)
        destruct He1 as [[[i1 | b1] He1] | He1].

            (* Case : EvalTo e1 (VInt i1) *)
            destruct He2 as [[[i2 | b2] He2] | He2].

                (* Case : EvalTo e2 (VInt i2) *)
                left.
                exists (VInt (i1 + i2)).
                apply (E_Plus _ _ _ _ _  He1 He2).
                apply B_Plus.
                reflexivity.

                (* Case : EvalTo e2 (VBool b2) *)
                right.
                apply (E_PlusBoolR _ _ _ He2).

                (* Case : Error e2 *)
                right.
                apply (E_PlusErrorR _ _ He2).

            (* Case : EvalTo e1 (VBool b1) *)
            right.
            apply (E_PlusBoolL _ _ _ He1).

            (* Case : Error e1 *)
            right.
            apply (E_PlusErrorL _ _ He1).

        (* Case : f = EMinux e1 e2 *)
        destruct He1 as [[[i1 | b1] He1] | He1].

            (* Case : EvalTo e1 (VInt i1) *)
            destruct He2 as [[[i2 | b2] He2] | He2].

                (* Case : EvalTo e2 (VInt i2) *)
                left.
                exists (VInt (i1 - i2)).
                apply (E_Minus _ _ _ _ _  He1 He2).
                apply B_Minus.
                reflexivity.

                (* Case : EvalTo e2 (VBool b2) *)
                right.
                apply (E_MinusBoolR _ _ _ He2).

                (* Case : Error e2 *)
                right.
                apply (E_MinusErrorR _ _ He2).

            (* Case : EvalTo e1 (VBool b1) *)
            right.
            apply (E_MinusBoolL _ _ _ He1).

            (* Case : Error e1 *)
            right.
            apply (E_MinusErrorL _ _ He1).

        (* Case : f = ETimes e1 e2 *)
        destruct He1 as [[[i1 | b1] He1] | He1].

            (* Case : EvalTo e1 (VInt i1) *)
            destruct He2 as [[[i2 | b2] He2] | He2].

                (* Case : EvalTo e2 (VInt i2) *)
                left.
                exists (VInt (i1 * i2)).
                apply (E_Times _ _ _ _ _  He1 He2).
                apply B_Times.
                reflexivity.

                (* Case : EvalTo e2 (VBool b2) *)
                right.
                apply (E_TimesBoolR _ _ _ He2).

                (* Case : Error e2 *)
                right.
                apply (E_TimesErrorR _ _ He2).

            (* Case : EvalTo e1 (VBool b1) *)
            right.
            apply (E_TimesBoolL _ _ _ He1).

            (* Case : Error e1 *)
            right.
            apply (E_TimesErrorL _ _ He1).

        (* Case : f = ELt e1 e2 *)
        destruct He1 as [[[i1 | b1] He1] | He1].

            (* Case : EvalTo e1 (VInt i1) *)
            destruct He2 as [[[i2 | b2] He2] | He2].

                (* Case : EvalTo e2 (VInt i2) *)
                left.
                exists (VBool (i1 <? i2)).
                apply (E_Lt _ _ _ _ _  He1 He2).
                apply B_Lt.
                reflexivity.

                (* Case : EvalTo e2 (VBool b2) *)
                right.
                apply (E_LtBoolR _ _ _ He2).

                (* Case : Error e2 *)
                right.
                apply (E_LtErrorR _ _ He2).

            (* Case : EvalTo e1 (VBool b1) *)
            right.
            apply (E_LtBoolL _ _ _ He1).

            (* Case : Error e1 *)
            right.
            apply (E_LtErrorL _ _ He1).
Qed.

End IntegersAndBooleans.

