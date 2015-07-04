Section Metatheorems.
Require Import NaturalNumbers.

(* Theorem 2.1 (1) *)
Theorem Plus_unit_l :
    forall n : peano, Plus Z n n.
Proof.
Admitted.

(* Theorem 2.1 (2) *)
Theorem Plus_unit_r :
    forall n : peano, Plus n Z n.
Proof.
Admitted.

(* Theorem 2.2 *)
Theorem Plus_uniq :
    forall n1 n2 n3 n4 : peano, Plus n1 n2 n3 -> Plus n1 n2 n4 -> n3 = n4.
Proof.
Admitted.

(* Theorem 2.3 *)
Theorem Plus_exists :
    forall n1 n2 : peano, exists n3 : peano, Plus n1 n2 n3.
Proof.
Admitted.

(* Theorem 2.4 *)
Theorem Plus_sym :
    forall n1 n2 n3 : peano, Plus n1 n2 n3 -> Plus n2 n1 n3.
Proof.
Admitted.

(* Theorem 2.5 *)
Theorem Plus_split :
    forall n1 n2 n3 n4 n5 : peano,
    Plus n1 n2 n4 -> Plus n4 n3 n5 ->
    exists n6 : peano, Plus n2 n3 n6 /\ Plus n1 n6 n5.
Proof.
Admitted.

(* Theorem 2.6 *)
Theorem Times_uniq :
    forall n1 n2 n3 n4 : peano, Times n1 n2 n3 -> Times n1 n2 n4 -> n3 = n4.
Proof.
Admitted.

(* Theorem 2.7 *)
Theorem Times_exists :
    forall n1 n2 : peano, exists n3 : peano, Times n1 n2 n3.
Proof.
Admitted.

(* Theorem 2.8 (1) *)
Theorem Times_zero_l :
    forall n : peano, Times Z n Z.
Proof.
Admitted.

(* Theorem 2.8 (2) *)
Theorem Times_zero_r :
    forall n : peano, Times n Z Z.
Proof.
Admitted.

(* Theorem 2.9 *)
Theorem Times_sym :
    forall n1 n2 n3 : peano, Times n1 n2 n3 -> Times n2 n1 n3.
Proof.
Admitted.

(* Theorem 2.10 *)
Theorem Times_split :
    forall n1 n2 n3 n4 n5 : peano,
    Times n1 n2 n4 -> Times n4 n3 n5 ->
    exists n6 : peano, Times n2 n3 n6 /\ Times n1 n6 n5.
Proof.
Admitted.

(* Theorem 2.11 (CompareNat1) *)
Theorem LessThan1_Z_Sn :
    forall n : peano, LessThan1 Z (S n).
Proof.
Admitted.

(* Theorem 2.11 (CompareNat2) *)
Theorem LessThan2_Z_Sn :
    forall n : peano, LessThan2 Z (S n).
Proof.
Admitted.

(* Theorem 2.11 (CompareNat3) *)
Theorem LessThan3_Z_Sn :
    forall n : peano, LessThan3 Z (S n).
Proof.
Admitted.

(* Theorem 2.12 (CompareNat1) *)
Theorem LessThan1_prev :
    forall n1 n2 : peano, LessThan1 (S n1) (S n2) -> LessThan1 n1 n2.
Proof.
Admitted.

(* Theorem 2.12 (CompareNat2) *)
Theorem LessThan2_prev :
    forall n1 n2 : peano, LessThan2 (S n1) (S n2) -> LessThan2 n1 n2.
Proof.
Admitted.

(* Theorem 2.12 (CompareNat3) *)
Theorem LessThan3_prev :
    forall n1 n2 : peano, LessThan3 (S n1) (S n2) -> LessThan3 n1 n2.
Proof.
Admitted.

(* Theorem 2.13 (CompareNat1 *)
Theorem LessThan1_trans :
    forall n1 n2 n3 : peano,
    LessThan1 n1 n2 -> LessThan1 n2 n3 -> LessThan1 n1 n3.
Proof.
Admitted.

(* Theorem 2.13 (CompareNat2 *)
Theorem LessThan2_trans :
    forall n1 n2 n3 : peano,
    LessThan2 n1 n2 -> LessThan2 n2 n3 -> LessThan2 n1 n3.
Proof.
Admitted.

(* Theorem 2.13 (CompareNat3 *)
Theorem LessThan3_trans :
    forall n1 n2 n3 : peano,
    LessThan3 n1 n2 -> LessThan3 n2 n3 -> LessThan3 n1 n3.
Proof.
Admitted.

(* Theorem 2.14 (1) (2) *)
Theorem LessThan_equiv_1_2 :
    forall n1 n2 : peano, LessThan1 n1 n2 <-> LessThan2 n1 n2.
Proof.
Admitted.

(* Theorem 2.14 (2) (3) *)
Theorem LessThan_equiv_2_3 :
    forall n1 n2 : peano, LessThan2 n1 n2 <-> LessThan3 n1 n2.
Proof.
Admitted.

(* Theorem 2.14 (1) (3) *)
Theorem LessThan_equiv_1_3 :
    forall n1 n2 : peano, LessThan1 n1 n2 <-> LessThan3 n1 n2.
Proof.
Admitted.

(* Theorem 2.15 *)
Theorem EvalTo_total :
    forall e : Exp, exists n : peano, EvalTo e n.
Proof.
Admitted.

(* Theorem 2.16 *)
Theorem EvalTo_uniq :
    forall (e : Exp) (n1 n2 : peano), EvalTo e n1 -> EvalTo e n2 -> n1 = n2.
Proof.
Admitted.

(* Theorem 2.17 *)
Theorem EPlus_comm :
    forall (e1 e2 : Exp) (n : peano),
    EvalTo (EPlus e1 e2) n -> EvalTo (EPlus e2 e1) n.
Proof.
Admitted.

(* Theorem 2.18 *)
Theorem EPlus_concat :
    forall (e1 e2 e3 : Exp) (n : peano),
    EvalTo (EPlus (EPlus e1 e2) e3) n -> EvalTo (EPlus e1 (EPlus e2 e3)) n.
Proof.
Admitted.

(* Theorem 2.19 *)
Theorem ETimes_comm :
    forall (e1 e2 : Exp) (n : peano),
    EvalTo (ETimes e1 e2) n -> EvalTo (ETimes e2 e1) n.
Proof.
Admitted.

(* Theorem 2.20 *)
Theorem ETimes_concat :
    forall (e1 e2 e3 : Exp) (n : peano),
    EvalTo (ETimes (ETimes e1 e2) e3) n -> EvalTo (ETimes e1 (ETimes e2 e3)) n.
Proof.
Admitted.

(* Theorem 2.21 *)
Theorem ReduceTo_progress :
    forall e : Exp,
    (exists n : peano, e = ENum n) \/ (exists e' : Exp, ReduceTo e e').
Proof.
Admitted.

(* Theorem 2.22 *)
Theorem ReduceTo_confl :
    forall e1 e2 e3 : Exp,
    ReduceTo e1 e2 -> ReduceTo e1 e3 ->
    exists e4 : Exp, ReduceTo e2 e4 /\ ReduceTo e3 e4.
Proof.
Admitted.

(* Theorem 2.23 *)
Theorem DetReduceTo_uniq :
    forall e e' e'' : Exp, ReduceTo e e' -> ReduceTo e e'' -> e' = e''.
Proof.
Admitted.

(* Theorem 2.24 *)
Theorem DetReduceTo_ReduceTo :
    forall e e' : Exp, DetReduceTo e e' -> ReduceTo e e'.
Proof.
Admitted.

(* Theorem 2.25 *)
Theorem ReduceTo_weak_normal :
    forall e : Exp, exists n : peano, MultiReduceTo e (ENum n).
Proof.
Admitted.

(* FIXME: Theorem 2.26 *)

(* Theorem 2.27 *)
Theorem EvalTo_MultiReduceTo :
    forall (e : Exp) (n : peano), EvalTo e n -> MultiReduceTo e (ENum n).
Proof.
Admitted.

(* Theorem 2.28 *)
Theorem MultiReduceTo_EvalTo :
    forall (e : Exp) (n : peano), MultiReduceTo e (ENum n) -> EvalTo e n.
Proof.
Admitted.

End Metatheorems.
