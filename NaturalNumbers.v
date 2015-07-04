Inductive peano : Set :=
    | Z : peano
    | S : peano -> peano.

(* Def 1.2 *)
Inductive Plus : peano -> peano -> peano -> Prop :=
    | P_Zero : forall n : peano, Plus Z n n
    | P_Succ : forall n1 n2 n3 : peano,
               Plus n1 n2 n3 -> Plus (S n1) n2 (S n3).

(* Def 1.3 *)
Inductive Times : peano -> peano -> peano -> Prop :=
    | T_Zero : forall n : peano, Times Z n Z
    | T_Succ : forall n1 n2 n3 n4 : peano,
               Times n1 n2 n3 -> Plus n2 n3 n4 -> Times (S n1) n2 n4.

(* Fig 1.3 *)
Inductive LessThan1 : peano -> peano -> Prop :=
    | L1_Succ  : forall n : peano, LessThan1 n (S n)
    | L1_Trans : forall n1 n2 n3 : peano,
                 LessThan1 n1 n2 -> LessThan1 n2 n3 -> LessThan1 n1 n3.

(* Fig 1.4 *)
Inductive LessThan2 : peano -> peano -> Prop :=
    | L2_Zero     : forall n : peano, LessThan2 Z (S n)
    | L2_SuccSucc : forall n1 n2 : peano,
                    LessThan2 n1 n2 -> LessThan2 (S n1) (S n2).

(* Fig 1.5 *)
Inductive LessThan3 : peano -> peano -> Prop :=
    | L3_Succ  : forall n : peano, LessThan3 n (S n)
    | L3_SuccR : forall n1 n2 : peano, LessThan3 n1 n2 -> LessThan3 n1 (S n2).

(* Def 1.5 *)
Inductive Exp : Set :=
    | ENum   : peano -> Exp
    | EPlus  : Exp -> Exp -> Exp
    | ETimes : Exp -> Exp -> Exp.

(* Fig 1.7 *)
Inductive EvalTo : Exp -> peano -> Prop :=
    | E_Const : forall n : peano, EvalTo (ENum n) n
    | E_Plus  : forall (e1 e2 : Exp) (n1 n2 n : peano),
                EvalTo e1 n1 -> EvalTo e2 n2 -> Plus n1 n2 n ->
                EvalTo (EPlus e1 e2) n
    | E_Times : forall (e1 e2 : Exp) (n1 n2 n : peano),
                EvalTo e1 n1 -> EvalTo e2 n2 -> Times n1 n2 n ->
                EvalTo (ETimes e1 e2) n.

(* Fig 1.8 *)
Inductive ReduceTo : Exp -> Exp -> Prop :=
    | R_Plus   : forall n1 n2 n3 : peano,
                 Plus n1 n2 n3 -> ReduceTo (EPlus (ENum n1) (ENum n2)) (ENum n3)
    | R_Timss  : forall n1 n2 n3 : peano,
                 Times n1 n2 n3 ->
                 ReduceTo (ETimes (ENum n1) (ENum n2)) (ENum n3)
    | R_PlusL  : forall e1 e1' e2 : Exp,
                 ReduceTo e1 e1' -> ReduceTo (EPlus e1 e2) (EPlus e1' e2)
    | R_PlusR  : forall e1 e2 e2' : Exp,
                 ReduceTo e2 e2' -> ReduceTo (EPlus e1 e2) (EPlus e1 e2')
    | R_TimesL : forall e1 e1' e2 : Exp,
                 ReduceTo e1 e1' -> ReduceTo (ETimes e1 e2) (ETimes e1' e2)
    | R_TimesR : forall e1 e2 e2' : Exp,
                 ReduceTo e2 e2' -> ReduceTo (ETimes e1 e2) (ETimes e1 e2').

(* Fig 1.9 *)
Inductive MultiReduceTo : Exp -> Exp -> Prop :=
    | MR_Zero  : forall e : Exp, MultiReduceTo e e
    | MR_One   : forall e e' : Exp, ReduceTo e e' -> MultiReduceTo e e'
    | MR_Multi : forall e e' e'' : Exp,
                 MultiReduceTo e e' -> MultiReduceTo e' e'' ->
                 MultiReduceTo e e''.

(* Fig 1.10 *)
Inductive DetReduceTo : Exp -> Exp -> Prop :=
    | DR_Plus   : forall n1 n2 n3 : peano,
                  Plus n1 n2 n3 ->
                  DetReduceTo (EPlus (ENum n1) (ENum n2)) (ENum n3)
    | DR_Times  : forall n1 n2 n3 : peano,
                  Times n1 n2 n3 ->
                  DetReduceTo (ETimes (ENum n1) (ENum n2)) (ENum n3)
    | DR_PlusL  : forall e1 e1' e2 : Exp,
                  DetReduceTo e1 e1' ->
                  DetReduceTo (EPlus e1 e2) (EPlus e1' e2)
    | DR_PlusR  : forall (n1 : peano) (e2 e2' : Exp),
                  DetReduceTo e2 e2' ->
                  DetReduceTo (EPlus (ENum n1) e2) (EPlus (ENum n1) e2')
    | DR_TimesL : forall e1 e1' e2 : Exp,
                  DetReduceTo e1 e1' ->
                  DetReduceTo (ETimes e1 e2) (ETimes e1' e2)
    | DR_TimesR : forall (n1 : peano) (e2 e2' : Exp),
                  DetReduceTo e2 e2' ->
                  DetReduceTo (ETimes (ENum n1) e2) (ETimes (ENum n1) e2').

