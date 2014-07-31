(** * Hoare triple for machine state monad *)
Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import Coq.Setoids.Setoid Coq.Program.Basics Coq.Classes.Morphisms.
Require Import x86proved.common_tactics.

Import Prenex Implicits.

Local Transparent ILFun_Ops ILPre_Ops.

Local Ltac fin_solve_morphism :=
  do !(idtac;
       match goal with
         | [ s : ProcState, H : forall _ : ProcState, _ |- _ ] => specialize (H s)
         | [ H : _ |- _ ] => (eapply H; eassumption)
         | [ H : _, H' : _ |- _ ] => (rewrite -> H in H'; clear H)
         | [ H : _, H' : _ |- _ ] => (rewrite <- H in H'; clear H)
         | [ H : _, H' : _ |- _ ] => (setoid_rewrite -> H in H'; clear H)
         | [ H : _, H' : _ |- _ ] => (setoid_rewrite <- H in H'; clear H)
         | [ H : _ |- _ ] => eapply H; eassumption
       end).

Local Ltac solve_morphism :=
  (rewrite /valued_TRIPLE/pointwise_relation => *; do ?move => ?);
  fin_solve_morphism.

(** Triples behave contravariantly in the precondition and covariantly
    in the postcondition wrt entailment *)
Global Add Parametric Morphism T v : (@valued_TRIPLE T v) with signature lentails --> eq ==> lentails ==> lentails ==> impl as TRIPLE_mor2.
Proof. solve_morphism. Qed.

Global Add Parametric Morphism T v : (@valued_TRIPLE T v) with signature lentails --> eq ==> eq ==> lentails ==> impl as TRIPLE_mor3.
Proof. move => * ?. fin_solve_morphism. Qed.

(** Unfortunately we need special case for equivalence *)
Global Add Parametric Morphism T v : (@valued_TRIPLE T v) with signature lequiv ==> eq ==> lequiv ==> lequiv ==> iff as TRIPLE_mor.
Proof. move => *; split => ?; fin_solve_morphism. Qed.

Global Add Parametric Morphism T v : (@valued_TRIPLE T v) with signature lequiv ==> eq ==> eq ==> lequiv ==> iff as TRIPLE_mor4.
Proof. move => *; split => ?; fin_solve_morphism. Qed.

(** For dealing with programs *)
Global Add Parametric Morphism T v P : (@valued_TRIPLE T v P) with signature (pointwise_relation ProcState eq) ==> eq ==> eq ==> impl as TRIPLE_morprogram.
Proof. solve_morphism. Qed.
