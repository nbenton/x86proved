(** * Predicates over observations (sequences of actions) *)
(** Basic definitions of observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.x86.ioaction x86proved.charge.csetoid.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Program.Basics.
(** Importing this file really only makes sense if you also import
    ilogic, so we force that. *)
Require Export x86proved.charge.ilogic x86proved.charge.bilogic x86proved.ilogicss.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*===========================================================================
    Predicates over observations (sequences of actions)
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.x86.ioaction x86proved.charge.ilogic.
Require Import Coq.Setoids.Setoid x86proved.charge.csetoid Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Program.Basics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Obligation Tactic := idtac.

(* We require predicates on observations to be non-empty i.e. for there to be
   some sequence of actions for which it holds *)
Record OPred := mkOPred {
  OPred_pred :> Actions -> Prop;
  OPred_inhabited: exists x: Actions, OPred_pred x
}.

Implicit Arguments mkOPred [].

(** ** Singleton predicate *)
Program Definition eq_opred s := mkOPred (fun s' => s === s') _.
Next Obligation. move => s. by exists s. Qed.

(** ** The empty sequence of actions *)
Definition empOP : OPred := eq_opred nil.

(** ** A single output action *)
Definition outOP (c:Chan) (d:Data) : OPred := eq_opred [::Out c d].

(** ** A sequence of actions that splits into the concatenation of one
satisfying P and one satisfying Q *)
Program Definition catOP (P Q: OPred) : OPred
 := mkOPred (fun o => exists o1 o2, o = o1++o2 /\ P o1 /\ Q o2) _.
Next Obligation.
move => [P [Px PH]] [Q [Qx QH]]. exists (Px++Qx). exists Px, Qx.
intuition.
Qed.

(** ** Any sequence of actions *)
Program Definition trueOP : OPred := @mkOPred (fun _ => True) _.
Next Obligation. by exists nil. Qed.

(** ** Union *)
Program Definition orOP (P Q: OPred) : OPred
  := mkOPred (fun o => P o \/ Q o) _.
Next Obligation.
move => [P [Px PH]] [Q [Qx QH]]. exists Px. by left.
Qed.

(** ** Repetition *)
Fixpoint repOP n P := if n is n.+1 then catOP P (repOP n P) else empOP.

(** ** Existential quantification, for inhabited types *)
Program Definition existsOP X {_: inhabited X} (f: X -> OPred) : OPred :=
  mkOPred (fun o => exists x: X, f x o) _.
Next Obligation.
move => X [x] f.
destruct (OPred_inhabited (f x)) as [y H]. by exists y, x.
Qed.

(** ** Kleene star *)
Definition starOP P := @existsOP _ (inhabits 0) (fun n => repOP n P).

(* *** Inclusion and equivalence on predicates *)
Definition entailsOP (O O': OPred) := forall s, O s -> O' s.
Definition equivOP (O O': OPred) := entailsOP O O' /\ entailsOP O' O.
