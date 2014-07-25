(** * Hoare triple for machine state monad *)
Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import Coq.Setoids.Setoid Coq.Program.Basics Coq.Classes.Morphisms.
Require Import x86proved.common_tactics.

Import Prenex Implicits.

Local Transparent ILFun_Ops ILPre_Ops.

Local Ltac solve_morphism :=
  rewrite /TRIPLE; do ?[ split | move => ? ];
  do 6?[ by do !esplit; eauto with nocore
       | by do !esplit; try hyp_rewrite <- *; eauto with nocore
       | progress destruct_head_hnf ex
       | progress destruct_head_hnf and
       | progress hnf in *; unfold lentails, ILFun_Ops, ILPre_Ops in *; hnf in *
       | progress specialize_all_ways ].

(** Triples behave contravariantly in the precondition and covariantly
    in the postcondition wrt entailment *)
Global Add Morphism (@TRIPLE) with signature lentails --> eq ==> lentails ==> lentails ==> impl as TRIPLE_mor2.
Proof. solve_morphism. Qed.

Global Add Morphism (@TRIPLE) with signature lentails --> eq ==> eq ==> lentails ==> impl as TRIPLE_mor3.
Proof. solve_morphism. Qed.

(** Unfortunately we need special case for equivalence *)
Global Add Morphism (@TRIPLE) with signature lequiv ==> eq ==> lequiv ==> lequiv ==> iff as TRIPLE_mor.
Proof. solve_morphism. Qed.

Add Morphism (@TRIPLE) with signature lequiv ==> eq ==> eq ==> lequiv ==> iff as TRIPLE_mor4.
Proof. solve_morphism. Qed.

(** For dealing with programs *)
Global Add Morphism (@TRIPLE) with signature eq --> (pointwise_relation ProcState eq) ==> eq ==> eq ==> impl as TRIPLE_morprogram.
Proof. solve_morphism. Qed.
