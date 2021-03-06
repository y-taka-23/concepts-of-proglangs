Section StaticScopes.
Require Import Functions.
Require Import ZArith.
Open Scope Z_scope.

(* Expressions with de Bruijn indices at p.97 and p.100 *)
(* The indices are 0-besed, unlike the definition in the text *)
Inductive DBExp : Set :=
    | DBEInt    : Z -> DBExp
    | DBEBool   : bool -> DBExp
    | DBEVar    : nat -> DBExp
    | DBEPlus   : DBExp -> DBExp -> DBExp
    | DBEMinus  : DBExp -> DBExp -> DBExp
    | DBETimes  : DBExp -> DBExp -> DBExp
    | DBELt     : DBExp -> DBExp -> DBExp
    | DBEIf     : DBExp -> DBExp -> DBExp -> DBExp
    | DBELet    : DBExp -> DBExp -> DBExp
    | DBEFun    : DBExp -> DBExp
    | DBEApp    : DBExp -> DBExp -> DBExp
    | DBELetRec : DBExp -> DBExp -> DBExp.

(* Values and environments *)
Inductive DBValue : Set :=
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
                  TransTo X (EInt i) (DBEInt i)
    | Tr_Bool   : forall (X : VarList) (b : bool),
                  TransTo X (EBool b) (DBEBool b)
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
                  TransTo X e1 d1 -> TransTo (VLCons X x) e2 d2 ->
                  TransTo X (ELet x e1 e2) (DBELet d1 d2)
    | Tr_Fun    : forall (X : VarList) (x : Var) (e : Exp) (d : DBExp),
                  TransTo (VLCons X x) e d ->
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
    | NV_O : forall (V : DBValueList) (w : DBValue),
             nth_val (DBVLCons V w) O w
    | NV_S : forall (V : DBValueList) (n : nat) (w w0 : DBValue),
             nth_val V n w ->
             nth_val (DBVLCons V w0) (S n) w.

(* Fig 6.3, 6.4 *)
Inductive DBEvalTo : DBValueList -> DBExp -> DBValue -> Prop :=
    | DBE_Int    : forall (V : DBValueList) (i : Z),
                   DBEvalTo V (DBEInt i) (DBVInt i)
    | DBE_Bool   : forall (V : DBValueList) (b : bool),
                   DBEvalTo V (DBEBool b) (DBVBool b)
    | DBE_IfT    : forall (V : DBValueList) (d1 d2 d3 : DBExp) (w : DBValue),
                   DBEvalTo V d1 (DBVBool true) -> DBEvalTo V d2 w ->
                   DBEvalTo V (DBEIf d1 d2 d3) w
    | DBE_IfF    : forall (V : DBValueList) (d1 d2 d3 : DBExp) (w : DBValue),
                   DBEvalTo V d1 (DBVBool false) -> DBEvalTo V d3 w ->
                   DBEvalTo V (DBEIf d1 d2 d3) w
    | DBE_Plus   : forall (V : DBValueList) (d1 d2 : DBExp) (i1 i2 i3 : Z),
                   DBEvalTo V d1 (DBVInt i1) -> DBEvalTo V d2 (DBVInt i2) ->
                   Plus i1 i2 i3 ->
                   DBEvalTo V (DBEPlus d1 d2) (DBVInt i3)
    | DBE_Minus  : forall (V : DBValueList) (d1 d2 : DBExp) (i1 i2 i3 : Z),
                   DBEvalTo V d1 (DBVInt i1) -> DBEvalTo V d2 (DBVInt i2) ->
                   Minus i1 i2 i3 ->
                   DBEvalTo V (DBEMinus d1 d2) (DBVInt i3)
    | DBE_Times  : forall (V : DBValueList) (d1 d2 : DBExp) (i1 i2 i3 : Z),
                   DBEvalTo V d1 (DBVInt i1) -> DBEvalTo V d2 (DBVInt i2) ->
                   Times i1 i2 i3 ->
                   DBEvalTo V (DBETimes d1 d2) (DBVInt i3)
    | DBE_Lt     : forall (V : DBValueList) (d1 d2 : DBExp)
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
                   DBEvalTo V d1 (DBVRecFun V2 d0) -> DBEvalTo V d2 w2 ->
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
    intros E X V e d v Htre Htr He.
    generalize dependent d.
    generalize dependent V.
    generalize dependent X.
    induction He as [ E i | E b | E x v | E x y v1 v2 Hneq Hv2 Hx |
                      E e1 e2 e3 i1 i2 i3 He1 He1' He2 He2' Hp |
                      E e1 e2 e3 i1 i2 i3 He1 He1' He2 He2' Hm |
                      E e1 e2 e3 i1 i2 i3 He1 He1' He2 He2' Ht |
                      E e1 e2 i1 i2 b3 He1 He1' He2 He2' Hl |
                      E e1 e2 e3 v2 He1 He1' He2 He2' |
                      E e1 e2 e3 v2 He1 He1' He3 He3' |
                      E e1 e2 x v1 v He1 He1' He2 He2' | E x e |
                      E E2 e1 e2 e0 x v v' He1 He1' He2 He2' He0 He0' |
                      E x y e1 e2 v He2 He2' |
                      E E2 e1 e2 e0 x y v v' He1 He1' He2 He2' He0 He0' ].

        (* Case : He is from E_Int *)
        intros X V Htre d Htr.
        inversion Htr; subst.
        exists (DBVInt i).
        apply (conj (DBE_Int _ _) (Trv_Int _)).

        (* Case : He is from E_Bool *)
        intros X V Htre d Htr.
        inversion Htr; subst.
        exists (DBVBool b).
        apply (conj (DBE_Bool _ _) (Trv_Bool _)).

        (* Case : He if from E_Var1 *)
        intros X V Htre d Htr.
        inversion Htr; subst.

            (* Case : Htr is from Tr_Var1 *)
            inversion Htre; subst.
            exists w.
            apply (conj (DBE_Var _ _ _ (NV_O _ _)) H5).

            (* Case : Htr is from Tr_Var2 *)
            inversion Htre; subst.
            contradict H0.
            reflexivity.

        (* Case : He is from E_Var2 *)
        intros X V Htre d Htr.
        inversion Htr; subst.

            (* Case : Htr is from Tr_Var1 *)
            inversion Htre; subst.
            contradict Hneq.
            reflexivity.

            (* Case : Htr is from Tr_Var2 *)
            inversion Htre; subst.
            specialize (Hx _ _ H7 _ H2).
            destruct Hx as [w' [Hw' Hx]].
            exists w'.
            inversion Hw'; subst.
            apply (conj (DBE_Var _ _ _ (NV_S _ _ _ _ H3)) Hx).

        (* Case : He is from E_Plus *)
        intros X V Htre d Htr.
        exists (DBVInt i3).
        inversion Htr; subst.
        specialize (He1' _ _ Htre d1 H2).
        destruct He1' as [w1 [Hw1 He1']].
        inversion He1'; subst.
        specialize (He2' _ _ Htre d2 H4).
        destruct He2' as [w2 [Hw2 He2']].
        inversion He2'; subst.
        apply (conj (DBE_Plus _ _ _ _ _ _ Hw1 Hw2 Hp)
                    (Trv_Int _)).

        (* Case : He is from E_Minus *)
        intros X V Htre d Htr.
        exists (DBVInt i3).
        inversion Htr; subst.
        specialize (He1' _ _ Htre d1 H2).
        destruct He1' as [w1 [Hw1 He1']].
        inversion He1'; subst.
        specialize (He2' _ _ Htre d2 H4).
        destruct He2' as [w2 [Hw2 He2']].
        inversion He2'; subst.
        apply (conj (DBE_Minus _ _ _ _ _ _ Hw1 Hw2 Hm)
                    (Trv_Int _)).

        (* Case : He is from E_Times *)
        intros X V Htre d Htr.
        exists (DBVInt i3).
        inversion Htr; subst.
        specialize (He1' _ _ Htre d1 H2).
        destruct He1' as [w1 [Hw1 He1']].
        inversion He1'; subst.
        specialize (He2' _ _ Htre d2 H4).
        destruct He2' as [w2 [Hw2 He2']].
        inversion He2'; subst.
        apply (conj (DBE_Times _ _ _ _ _ _ Hw1 Hw2 Ht)
                    (Trv_Int _)).

        (* Case : He is from E_Lt *)
        intros X V Htre d Htr.
        exists (DBVBool b3).
        inversion Htr; subst.
        specialize (He1' _ _ Htre d1 H2).
        destruct He1' as [w1 [Hw1 He1']].
        inversion He1'; subst.
        specialize (He2' _ _ Htre d2 H4).
        destruct He2' as [w2 [Hw2 He2']].
        inversion He2'; subst.
        apply (conj (DBE_Lt _ _ _ _ _ _ Hw1 Hw2 Hl)
                    (Trv_Bool _)).

        (* Case : He is from E_IfT *)
        intros X V Htre d Htr.
        inversion Htr; subst.
        specialize (He1' _ _ Htre d1 H3).
        destruct He1' as [w1 [Hw1 He1']].
        inversion He1'; subst.
        specialize (He2' _ _ Htre d2 H5).
        destruct He2' as [w2 [Hw2 He2']].
        exists w2.
        apply (conj (DBE_IfT _ _ _ _ _ Hw1 Hw2) He2').

        (* Case : He is from E_IfF *)
        intros X V Htre d Htr.
        inversion Htr; subst.
        specialize (He1' _ _ Htre d1 H3).
        destruct He1' as [w1 [Hw1 He1']].
        inversion He1'; subst.
        specialize (He3' _ _ Htre d3 H6).
        destruct He3' as [w3 [Hw3 He3']].
        exists w3.
        apply (conj (DBE_IfF _ _ _ _ _ Hw1 Hw3) He3').

        (* Case : He is from E_Let *)
        intros X V Htre d Htr.
        inversion Htr; subst.
        specialize (He1' _ _ Htre d1 H4).
        destruct He1' as [w1 [Hw1 He1']].
        specialize (He2' _ _ (Tre_Bind _ _ _ _ _ _ Htre He1') d2 H5).
        destruct He2' as [w2 [Hw2 He2']].
        exists w2.
        apply (conj (DBE_Let _ _ _ _ _ Hw1 Hw2) He2').

        (* Case : He is from E_Fun *)
        intros X V Htre d Htr.
        inversion Htr; subst.
        exists (DBVFun V d0).
        apply (conj (DBE_Fun _ _) ((Trv_Fun _ _ _ _ _ _ Htre H3))).

        (* Case : He is from E_App *)
        intros X V Htre d Htr.
        inversion Htr; subst.
        specialize (He1' _ _ Htre d1 H2).
        destruct He1' as [w1 [Hw1 He1']].
        inversion He1'; subst.
        specialize (He2' _ _ Htre d2 H4).
        destruct He2' as [w2 [Hw2 He2']].
        specialize (He0' _ _ (Tre_Bind _ _ _ _ _ _ H5 He2') d H6).
        destruct He0' as [w0 [Hw0 He0']].
        exists w0.
        apply (conj (DBE_App _ V0 _ _ d _ w2 Hw1 Hw2 Hw0) He0').

        (* Case : He is from E_LetRec *)
        intros X V Htre d Htr.
        inversion Htr; subst.
        assert (TransEnvTo (ECons E x (VRecFun E x y e1))
                           (VLCons X x) (DBVLCons V (DBVRecFun V d1))) as Hd1
            by apply (Tre_Bind _ _ _ _ _ _
                               Htre (Trv_Rec _ X _ _ _ _ _ Htre H5)).
        specialize (He2' _ _ Hd1 _ H6).
        destruct He2' as [w2 [Hw2 He2']].
        exists w2.
        apply (conj (DBE_LetRec _ _ _ _ Hw2) He2').

        (* Case : He is from E_AppRec *)
        intros X V Htre d Htr.
        inversion Htr; subst.
        specialize (He1' _ _ Htre _ H2).
        destruct He1' as [w1 [Hw1 He1']].
        inversion He1'; subst.
        specialize (He2' _ _ Htre _ H4).
        destruct He2' as [w2 [Hw2 He2']].
        assert (TransEnvTo (ECons (ECons E2 x (VRecFun E2 x y e0)) y v')
                           (VLCons (VLCons X0 x) y)
                           (DBVLCons (DBVLCons V0 (DBVRecFun V0 d)) w2)) as Hd.

            (* Proof of the assertion *)
            refine (Tre_Bind _ _ _ _ _ _ _ He2').
            apply (Tre_Bind _ _ _ _ _ _ H6 (Trv_Rec _ _ _ _ _ _ _ H6 H7)).

        specialize (He0' _ _ Hd _ H7).
        destruct He0' as [w0 [Hw0 He0']].
        exists w0.
        apply (conj (DBE_AppRec _ _ _ _ _ _ _ Hw1 Hw2 Hw0) He0').
Qed.

(* Theorem 6.1 (2) *)
Theorem DBEvalTo_EvalTo_compat :
    forall (E : Env) (X : VarList) (V : DBValueList)
           (e : Exp) (d : DBExp) (w : DBValue),
    TransEnvTo E X V -> TransTo X e d -> DBEvalTo V d w ->
    exists v : Value, (EvalTo E e v /\ TransValTo v w).
Proof.
    intros E X V e d w Htre Htr Hd.
    generalize dependent e.
    generalize dependent X.
    generalize dependent E.
    induction Hd as [ V i | V b |
                      V d1 d2 d3 w Hd1 Hd1' Hd2 Hd2' |
                      V d1 d2 d3 w Hd1 Hd1' Hd3 Hd3' |
                      V d1 d2 i1 i2 i3 Hd1 Hd1' Hd2 Hd2' Hp |
                      V d1 d2 i1 i2 i3 Hd1 Hd1' Hd2 Hd2' Hm |
                      V d1 d2 i1 i2 i3 Hd1 Hd1' Hd2 Hd2' Ht |
                      V d1 d2 i1 i2 b3 Hd1 Hd1' Hd2 Hd2' Hl |
                      V n w Hw | V d1 d2 w w1 Hd1 Hd1' Hd2 Hd2' | V d |
                      V V2 d1 d2 d0 w w2 Hd1 Hd1' Hd2 Hd2' Hd0 Hd0' |
                      V d1 d2 w Hd2 Hd2' |
                      V V2 d1 d2 d0 w w2 Hd1 Hd1' Hd2 Hd2' Hd0 Hd0' ].

        (* Case : Hd is from DBE_Int *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        exists (VInt i).
        apply (conj (E_Int _ _) (Trv_Int _)).

        (* Case : Hd is from DBE_Bool *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        exists (VBool b).
        apply (conj (E_Bool _ _) (Trv_Bool _)).

        (* Case : Hd is from DBE_IfT *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd1' _ _ Htre _ H4).
        destruct Hd1' as [v1 [Hv1 Hd1']].
        inversion Hd1'; subst.
        specialize (Hd2' _ _ Htre _ H5).
        destruct Hd2' as [v2 [Hv2 Hd2']].
        exists v2.
        apply (conj (E_IfT _ _ _ _ _ Hv1 Hv2) Hd2').

        (* Case : Hd is from DBE_IfF *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd1' _ _ Htre _ H4).
        destruct Hd1' as [v1 [Hv1 Hd1']].
        inversion Hd1'; subst.
        specialize (Hd3' _ _ Htre _ H6).
        destruct Hd3' as [v3 [Hv3 Hd3']].
        exists v3.
        apply (conj (E_IfF _ _ _ _ _ Hv1 Hv3) Hd3').

        (* Case : Hd is from DBE_Plus *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd1' _ _ Htre _ H3).
        destruct Hd1' as [v1 [Hv1 Hd1']].
        inversion Hd1'; subst.
        specialize (Hd2' _ _ Htre _ H4).
        destruct Hd2' as [v1 [Hv2 Hd2']].
        inversion Hd2'; subst.
        exists (VInt i3).
        apply (conj (E_Plus _ _ _ (EInt i3) _ _ _ Hv1 Hv2 Hp)
                    (Trv_Int _)).

        (* Case : Hd is from DBE_Minus *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd1' _ _ Htre _ H3).
        destruct Hd1' as [v1 [Hv1 Hd1']].
        inversion Hd1'; subst.
        specialize (Hd2' _ _ Htre _ H4).
        destruct Hd2' as [v1 [Hv2 Hd2']].
        inversion Hd2'; subst.
        exists (VInt i3).
        apply (conj (E_Minus _ _ _ (EInt i3) _ _ _ Hv1 Hv2 Hm)
                    (Trv_Int _)).

        (* Case : Hd is from DBE_Times *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd1' _ _ Htre _ H3).
        destruct Hd1' as [v1 [Hv1 Hd1']].
        inversion Hd1'; subst.
        specialize (Hd2' _ _ Htre _ H4).
        destruct Hd2' as [v1 [Hv2 Hd2']].
        inversion Hd2'; subst.
        exists (VInt i3).
        apply (conj (E_Times _ _ _ (EInt i3) _ _ _ Hv1 Hv2 Ht)
                    (Trv_Int _)).

        (* Case : Hd is from DBE_Lt *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd1' _ _ Htre _ H3).
        destruct Hd1' as [v1 [Hv1 Hd1']].
        inversion Hd1'; subst.
        specialize (Hd2' _ _ Htre _ H4).
        destruct Hd2' as [v1 [Hv2 Hd2']].
        inversion Hd2'; subst.
        exists (VBool b3).
        apply (conj (E_Lt _ _ _ _ _ b3 Hv1 Hv2 Hl)
                    (Trv_Bool _)).

        (* Case : Hd is from DBE_Var *)
        induction Hw as [V0 w | V0 n0 w0 w Hw Hn0'].

            (* Case : Hw is from NV_O *)
            intros E X Htre e Htr.
            inversion Htr; subst.
            inversion Htre; subst.
            exists v.
            apply (conj (E_Var1 _ _ _) H5).

            (* Case : Hw is from NV_S *)
            intros E X Htre e Htr.
            inversion Htr; subst.
            inversion Htre; subst.
            specialize (Hn0' _ _ H5 _ H3).
            destruct Hn0' as [v0 [Hv0 Hn0']].
            exists v0.
            apply (conj (E_Var2 _ _ _ _ _ (not_eq_sym H0) Hv0) Hn0').

        (* Case : Hd is from DBE_Let *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd1' _ _ Htre _ H3).
        destruct Hd1' as [v1 [Hv1 Hd1']].
        specialize (Hd2' _ _ (Tre_Bind _ _ _ _ _ _ Htre Hd1') _ H4).
        destruct Hd2' as [v2 [Hv2 Hd2']].
        exists v2.
        apply (conj (E_Let _ _ _ _ _ _ Hv1 Hv2) Hd2').

        (* Case : Hd is from DBE_Fun *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        exists (VFun E x e0).
        apply (conj (E_Fun _ _ _) (Trv_Fun _ _ _ _ _ _ Htre H2)).

        (* Case : Hd is from DBE_App *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd1' _ _ Htre _ H3).
        destruct Hd1' as [v1 [Hv1 Hd1']].
        inversion Hd1'; subst.
        specialize (Hd2' _ _ Htre _ H4).
        destruct Hd2' as [v2 [Hv2 Hd2']].
        specialize (Hd0' _ _ (Tre_Bind _ _ _ _ _ _ H2 Hd2') _ H5).
        destruct Hd0' as [v0 [Hv0 Hd0']].
        exists v0.
        apply (conj (E_App _ _ _ _ _ _ _ _ Hv1 Hv2 Hv0) Hd0').

        (* Case : Hd is from DBE_LetRec *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd2' _ _ (Tre_Bind _ _ _ _ _ _ Htre
                              (Trv_Rec _ _ _ _ _ _ _ Htre H3))
                         _ H4).
        destruct Hd2' as [v2 [Hv2 Hd2']].
        exists v2.
        apply (conj (E_LetRec _ _ _ _ _ _ Hv2) Hd2').

        (* Case : Hd is from DBE_AppRec *)
        intros E X Htre e Htr.
        inversion Htr; subst.
        specialize (Hd1' _ _ Htre _ H3).
        destruct Hd1' as [v1 [Hv1 Hd1']].
        inversion Hd1'; subst.
        specialize (Hd2' _ _ Htre _ H4).
        destruct Hd2' as [v2 [Hv2 Hd2']].
        assert (TransEnvTo (ECons (ECons E0 x (VRecFun E0 x y e)) y v2)
                           (VLCons (VLCons X0 x) y)
                           (DBVLCons (DBVLCons V2 (DBVRecFun V2 d0)) w2)) as He.

            (* Proof of the assertion *)
            refine (Tre_Bind _ _ _ _ _ _ _ Hd2').
            apply (Tre_Bind _ _ _ _ _ _ H2 Hd1').

        specialize (Hd0' _ _ He _ H5).
        destruct Hd0' as [v0 [Hv0 Hd0']].
        exists v0.
        apply (conj (E_AppRec _ _ _ _ _ _ _ _ _ Hv1 Hv2 Hv0) Hd0').
Qed.

(* Free variables (omitted in the text) *)
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
                   is_FV e2 x -> x <> y -> is_FV (ELet y e1 e2) x
    | FV_Fun     : forall (e : Exp) (x y : Var),
                   is_FV e x -> x <> y -> is_FV (EFun y e) x
    | FV_App_l   : forall (e1 e2 : Exp) (x : Var),
                   is_FV e1 x -> is_FV (EApp e1 e2) x
    | FV_App_r   : forall (e1 e2 : Exp) (x : Var),
                   is_FV e2 x -> is_FV (EApp e1 e2) x
    | FV_LetRec1 : forall (e1 e2 : Exp) (x y z : Var),
                   is_FV e1 x -> is_FV (ELetRec y z e1 e2) x
    | FV_LetRec2 : forall (e1 e2 : Exp) (x y z : Var),
                   is_FV e2 x -> x <> y ->
                   is_FV (ELetRec y z e1 e2) x.

(* Contents of ValueList *)
Inductive in_VL : VarList -> Var -> Prop :=
    | VL_Cons1 : forall (X : VarList) (x : Var), in_VL (VLCons X x) x
    | VL_Cons2 : forall (X : VarList) (x y : Var),
                 in_VL X x -> in_VL (VLCons X y) x.

Lemma Var_eq_dec :
    forall x y : Var, {x = y} + {x <> y}.
Proof.
    intros x y.
    destruct x as [n1].
    destruct y as [n2].
    destruct (eq_nat_dec n1 n2).

        (* Case : n1 = n2 *)
        left.
        subst; reflexivity.

        (* Case : n1 <> n2 *)
        right.
        intro F.
        inversion F.
        contradiction.
Qed.

(* Theorem 6.2 *)
Theorem TransTo_total :
    forall (X : VarList) (e : Exp),
    (forall x : Var, is_FV e x -> in_VL X x) ->
    exists d : DBExp, TransTo X e d.
Proof.
    intros X e.
    generalize dependent X.
    induction e as [ i | b | x |
                     e1 He1 e2 He2 | e1 He1 e2 He2 | e1 He1 e2 He2 |
                     e1 He1 e2 He2 | e1 He1 e2 He2 e3 He3 | x e1 He1 e2 He2 |
                     x e0 He0 | e1 He1 e2 He2 | x y e1 He1 e2 He2 ].

        (* Case : e = EInt i *)
        intros X HFV.
        exists (DBEInt i).
        apply Tr_Int.

        (* Case : e = EBool b *)
        intros X HFV.
        exists (DBEBool b).
        apply Tr_Bool.

        (* Case : e = EVar x *)
        induction X as [| X0 HX0 x0 ].

            (* Case : X = VLNil *)
            intro HFV.
            specialize (HFV x (FV_Var _)).
            inversion HFV.

            (* Case : X = VLCons X0 x0 *)
            intro HFV.
            specialize (HFV x (FV_Var _)).
            destruct (Var_eq_dec x0 x) as [Heq | Hneq].

                (* Case : x0 = x *)
                subst.
                exists (DBEVar 0).
                apply Tr_Var1.

                (* Case : x0 <> x *)
                assert (exists d : DBExp, TransTo X0 (EVar x) d) as Hd.

                    (* Proof of the assertion *)
                    apply HX0.
                    intros x1 Hx1.
                    inversion HFV; subst.

                        (* Case : HFV is from VL_Cons1 *)
                        contradict Hneq.
                        reflexivity.

                        (* Case : HFV is from VL_Cons2 *)
                        inversion Hx1; subst.
                        apply H2.

                destruct Hd as [d Hd].
                inversion Hd; subst.

                    (* Case : Hd is from Tr_Var1 *)
                    exists (DBEVar 1).
                    apply (Tr_Var2 _ _ _ _ Hneq Hd).

                    (* Case : Hd is from Tr_Var2 *)
                    exists (DBEVar (S (S n1))).
                    apply (Tr_Var2 _ _ _ _ Hneq Hd).

        (* Case : e = EPlus e1 e2 *)
        intros X HFV.
        assert (exists d : DBExp, TransTo X e1 d) as Hd1.

            (* Proof of the assertion *)
            apply He1.
            intros x0 H1.
            apply (HFV _ (FV_Plus_l _ _ _ H1)).

        assert (exists d : DBExp, TransTo X e2 d) as Hd2.

            (* Proof of the assertion *)
            apply He2.
            intros x0 H2.
            apply (HFV _ (FV_Plus_r _ _ _ H2)).

        destruct Hd1 as [d1 Hd1].
        destruct Hd2 as [d2 Hd2].
        exists (DBEPlus d1 d2).
        apply (Tr_Plus _ _ _ _ _ Hd1 Hd2).

        (* Case : e = EMinus e1 e2 *)
        intros X HFV.
        assert (exists d : DBExp, TransTo X e1 d) as Hd1.

            (* Proof of the assertion *)
            apply He1.
            intros x0 H1.
            apply (HFV _ (FV_Minus_l _ _ _ H1)).

        assert (exists d : DBExp, TransTo X e2 d) as Hd2.

            (* Proof of the assertion *)
            apply He2.
            intros x0 H2.
            apply (HFV _ (FV_Minus_r _ _ _ H2)).

        destruct Hd1 as [d1 Hd1].
        destruct Hd2 as [d2 Hd2].
        exists (DBEMinus d1 d2).
        apply (Tr_Minus _ _ _ _ _ Hd1 Hd2).

        (* Case : e = ETimes e1 e2 *)
        intros X HFV.
        assert (exists d : DBExp, TransTo X e1 d) as Hd1.

            (* Proof of the assertion *)
            apply He1.
            intros x0 H1.
            apply (HFV _ (FV_Times_l _ _ _ H1)).

        assert (exists d : DBExp, TransTo X e2 d) as Hd2.

            (* Proof of the assertion *)
            apply He2.
            intros x0 H2.
            apply (HFV _ (FV_Times_r _ _ _ H2)).

        destruct Hd1 as [d1 Hd1].
        destruct Hd2 as [d2 Hd2].
        exists (DBETimes d1 d2).
        apply (Tr_Times _ _ _ _ _ Hd1 Hd2).

        (* Case : e = ELt e1 e2 *)
        intros X HFV.
        assert (exists d : DBExp, TransTo X e1 d) as Hd1.

            (* Proof of the assertion *)
            apply He1.
            intros x0 H1.
            apply (HFV _ (FV_Lt_l _ _ _ H1)).

        assert (exists d : DBExp, TransTo X e2 d) as Hd2.

            (* Proof of the assertion *)
            apply He2.
            intros x0 H2.
            apply (HFV _ (FV_Lt_r _ _ _ H2)).

        destruct Hd1 as [d1 Hd1].
        destruct Hd2 as [d2 Hd2].
        exists (DBELt d1 d2).
        apply (Tr_Lt _ _ _ _ _ Hd1 Hd2).

        (* Case : e = EIf e1 e2 *)
        intros X HFV.
        assert (exists d : DBExp, TransTo X e1 d) as Hd1.

            (* Proof of the assertion *)
            apply He1.
            intros x0 H1.
            apply (HFV _ (FV_If _ _ _ _ H1)).

        assert (exists d : DBExp, TransTo X e2 d) as Hd2.

            (* Proof of the assertion *)
            apply He2.
            intros x0 H2.
            apply (HFV _ (FV_IfT _ _ _ _ H2)).

        assert (exists d : DBExp, TransTo X e3 d) as Hd3.

            (* Proof of the assertion *)
            apply He3.
            intros x0 H3.
            apply (HFV _ (FV_IfF _ _ _ _ H3)).

        destruct Hd1 as [d1 Hd1].
        destruct Hd2 as [d2 Hd2].
        destruct Hd3 as [d3 Hd3].
        exists (DBEIf d1 d2 d3).
        apply (Tr_If _ _ _ _ _ _ _ Hd1 Hd2 Hd3).

        (* Case : e = ELet e1 e2 *)
        intros X HFV.
        assert (exists d : DBExp, TransTo X e1 d) as Hd1.

            (* Proof of the assertion *)
            apply He1.
            intros x0 H1.
            apply (HFV _ (FV_Let1 _ _ _ _ H1)).

        assert (exists d : DBExp, TransTo (VLCons X x) e2 d) as Hd2.

            (* Proof of the assertion *)
            apply He2.
            intros x0 H2.
            destruct (Var_eq_dec x0 x) as [Heq | Hneq].

                (* Case : x0 = x *)
                subst.
                apply VL_Cons1.

                (* Case : x0 <> x *)
                apply VL_Cons2.
                apply (HFV _ (FV_Let2 _ _ _ _ H2 Hneq)).

        destruct Hd1 as [d1 Hd1].
        destruct Hd2 as [d2 Hd2].
        exists (DBELet d1 d2).
        apply (Tr_Let _ _ _ _ _ _ Hd1 Hd2).

        (* Case : e = EFun x e0 *)
        intros X HFV.
        assert (exists d : DBExp, TransTo (VLCons X x) e0 d) as Hd0.

            (* Proof of the assertion *)
            apply He0.
            intros x0 H0.
            destruct (Var_eq_dec x0 x) as [Heq | Hneq].

                (* Case : x0 = x *)
                subst.
                apply VL_Cons1.

                (* Case : x0 <> x *)
                apply VL_Cons2.
                apply (HFV _ (FV_Fun _ _ _ H0 Hneq)).

        destruct Hd0 as [d0 Hd0].
        exists (DBEFun d0).
        apply (Tr_Fun _ _ _ _ Hd0).

        (* Case : e = EApp e1 e2 *)
        intros X HFV.
        assert (exists d : DBExp, TransTo X e1 d) as Hd1.

            (* Proof of the assertion *)
            apply He1.
            intros x0 H1.
            apply (HFV _ (FV_App_l _ _ _ H1)).

        assert (exists d : DBExp, TransTo X e2 d) as Hd2.

            (* Proof of the assertion *)
            apply He2.
            intros x0 H2.
            apply (HFV _ (FV_App_r _ _ _ H2)).

        destruct Hd1 as [d1 Hd1].
        destruct Hd2 as [d2 Hd2].
        exists (DBEApp d1 d2).
        apply (Tr_App _ _ _ _ _ Hd1 Hd2).

        (* Case : e = ELetRec x y e1 e2 *)
        intros X HFV.
        assert (exists d : DBExp, TransTo (VLCons (VLCons X x) y) e1 d) as Hd1.

            (* Proof of the assertion *)
            apply He1.
            intros x0 H1.
            repeat apply VL_Cons2.
            apply (HFV _ (FV_LetRec1 _ _ _ _ _ H1)).

        assert (exists d : DBExp, TransTo (VLCons X x) e2 d) as Hd2.

            (* Proof of the assertion *)
            apply He2.
            intros x0 H2.
            destruct (Var_eq_dec x0 x) as [Heq | Hneq].

                (* Case : x0 = x *)
                subst.
                apply VL_Cons1.

                (* Case : x0 <> x *)
                apply VL_Cons2.
                apply (HFV _ (FV_LetRec2 _ _ _ _ _ H2 Hneq)).

        destruct Hd1 as [d1 Hd1].
        destruct Hd2 as [d2 Hd2].
        exists (DBELetRec d1 d2).
        apply (Tr_LetRec _ _ _ _ _ _ _ Hd1 Hd2).
Qed.

(* Theorem 6.3 *)
Theorem TransTo_uniq :
    forall (X : VarList) (e : Exp) (d1 d2 : DBExp),
    TransTo X e d1 -> TransTo X e d2 -> d1 = d2.
Proof.
    intros X e.
    generalize dependent X.
    induction e as [ i | b | x |
                     e1 He1 e2 He2 | e1 He1 e2 He2 | e1 He1 e2 He2 |
                     e1 He1 e2 He2 | e1 He1 e2 He2 e3 He3 | x e1 He1 e2 He2 |
                     x e0 He0 | e1 He1 e2 He2 | x y e1 He1 e2 He2 ].

        (* Case : e = EInt i *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        reflexivity.

        (* Case : e = EBool b *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        reflexivity.

        (* Case : e = EVar x *)
        induction X as [| X0 HX0 x0].

            (* Case : X = VLNil *)
            intros d1 d2 Hd1 Hd2.
            inversion Hd1.

            (* Case : X = VLCons X0 x0 *)
            intros d1 d2 Hd1 Hd2.
            inversion Hd1; subst.

                (* Case : Hd1 is from Tr_Var1 *)
                inversion Hd2; subst.

                    (* Case : Hd2 is from Tr_Var1 *)
                    reflexivity.

                    (* Case : Hd2 is from Tr_Var2 *)
                    contradict H2.
                    reflexivity.

                (* Case : Hd2 is from Tr_Var2 *)
                inversion Hd2; subst.

                    (* Case : Hd2 is from Tr_Var1 *)
                    contradict H2.
                    reflexivity.

                    (* Case : Hd2 is from Tr_Var2 *)
                    specialize (HX0 _ _ H4 H6).
                    inversion HX0; subst.
                    reflexivity.

        (* Case : e = EPlus e1 e2 *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        specialize (He1 _ _ _ H2 H3); subst.
        specialize (He2 _ _ _ H4 H6); subst.
        reflexivity.

        (* Case : e = EMinus e1 e2 *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        specialize (He1 _ _ _ H2 H3); subst.
        specialize (He2 _ _ _ H4 H6); subst.
        reflexivity.

        (* Case : e = ETimes e1 e2 *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        specialize (He1 _ _ _ H2 H3); subst.
        specialize (He2 _ _ _ H4 H6); subst.
        reflexivity.

        (* Case : e = ELt e1 e2 *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        specialize (He1 _ _ _ H2 H3); subst.
        specialize (He2 _ _ _ H4 H6); subst.
        reflexivity.

        (* Case : e = EIf e1 e2 e3 *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        specialize (He1 _ _ _ H3 H4); subst.
        specialize (He2 _ _ _ H5 H8); subst.
        specialize (He3 _ _ _ H6 H9); subst.
        reflexivity.

        (* Case : e = ELet x e1 e2 *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        specialize (He1 _ _ _ H4 H6); subst.
        specialize (He2 _ _ _ H5 H7); subst.
        reflexivity.

        (* Case : e = EFun x e0 *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        specialize (He0 _ _ _ H3 H4); subst.
        reflexivity.

        (* Case : e = EApp e1 e2 *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        specialize (He1 _ _ _ H2 H3); subst.
        specialize (He2 _ _ _ H4 H6); subst.
        reflexivity.

        (* Case : e = ELetRec x y e1 e2 *)
        intros X d1 d2 Hd1 Hd2.
        inversion Hd1; subst.
        inversion Hd2; subst.
        specialize (He1 _ _ _ H5 H7); subst.
        specialize (He2 _ _ _ H6 H8); subst.
        reflexivity.
Qed.

End StaticScopes.

