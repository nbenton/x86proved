(** * Morphisms for predicates over observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.x86.ioaction.
Require Import x86proved.opred.core.
Require Import x86proved.common_tactics.
(** We want access to the relations about lists in any file that might fold [catOP] *)
Require Export x86proved.list_relations.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.

Generalizable All Variables.
Set Implicit Arguments.

Local Transparent ILFun_Ops ILPre_Ops osepILogicOps osepILogic lentails ltrue lfalse limpl land lor lforall lexists.
Local Transparent catOP eq_opred.

Local Ltac t :=
  do ![ move => ?
      | progress destruct_head_hnf ex
      | progress destruct_head_hnf and
      | progress destruct_head_hnf or
      | progress subst
      | esplit
      | by hyp_apply *
      | by left; hyp_apply *
      | by right; hyp_apply * ].

Add Parametric Morphism : catOP with signature lentails ==> lentails ==> lentails as catOP_entails_m.
Proof. t. Qed.

Add Parametric Morphism : catOP with signature lequiv ==> lequiv ==> lequiv as catOP_equiv_m.
Proof. t. Qed.

Lemma foldr_catOP_map_respects_lentails {T} o0 f g (ls : seq T)
      (H : forall x, f x |-- g x)
: foldr catOP o0 (map f ls) |-- foldr catOP o0 (map g ls).
Proof.
  change ((pointwise_relation T (@lentails OPred _))%signature f g) in H.
  by rewrite -> H.
Qed.
