(** * Various tactics for dealing with charge logics and separation logics. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.common_tactics.
Require Import x86proved.charge.ilogic x86proved.charge.sepalg x86proved.charge.bilogic x86proved.charge.later x86proved.charge.csetoid.
Require Import x86proved.spec.
Require Import Coq.Setoids.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Generalizable All Variables.

Ltac simpl_logic' :=
  idtac;
  match goal with
    | [ |- appcontext[?x == ?x] ] => rewrite (eq_refl x)
    | [ |- ltrue //\\ _ |-- _ ] => apply: landL2
    | [ |- _ //\\ ltrue |-- _ ] => apply: landL1
    | [ |- _ |-- ltrue ] => apply ltrueR
    | [ |- _ |-- _ -->> _ ] => apply: limplAdj
    | [ |- _ /\ _ ] => split
    | [ |- ?a @ ?b |-- ?a @ ?b' ] => f_cancel
    | [ |- ?a <@ ?b |-- ?a' <@ ?b ] => f_cancel
    | [ |- ?P //\\ ?Q |-- ?P ] => apply: (@landL1 _ _ _ P Q P (reflexivity _))
    | [ |- _ -|- _ ] => split
    | [ |- _ -> _ ] => move => ?
  end.

Ltac simpl_logic := do ?simpl_logic'.

(** When dealing with logic, we want to reduce [stateIs] and similar to basic building blocks. *)
(** We put the hints in the file where each of these constants is defined. *)
(**
<<
Hint Unfold DWORDorBYTEregIs stateIsAny OSZCP stateIs : finish_logic_unfolder.
>>*)

Ltac finish_logic_with' tac :=
  idtac;
  match goal with
    | [ |- _ |-- _ <@ _ ] => progress rewrite <- spec_reads_frame
    | [ |- appcontext[(?P -->> ?Q) //\\ ?P] ] => setoid_rewrite (@landAdj _ _ _ P Q _ (reflexivity _))
    | _ => progress simpl_logic
    | _ => progress autorewrite with push_at
    | _ => progress repeat autounfold with finish_logic_unfolder
    | _ => progress tac
  end.
Ltac finish_logic_with tac := do ?finish_logic_with' tac.
Ltac finish_logic' := finish_logic_with' fail.
Ltac finish_logic := finish_logic_with fail.

Lemma triple_limpl `{@ILogic Frm ILOps'} (A B C : Frm) :  B -->> C |-- ((A -->> B) -->> A -->> C).
Proof.
  repeat match goal with
           | _ => progress simpl_logic
           | [ |- (?A //\\ ?B) //\\ ?C |-- _ ] => rewrite (landA A B C)
           | [ |- appcontext[(?P -->> ?Q) //\\ ?P] ] => setoid_rewrite (@landAdj _ _ _ P Q _ (reflexivity _))
           | _ => by apply landAdj
           | _ => syntax_unify_reflexivity
         end.
Qed.
