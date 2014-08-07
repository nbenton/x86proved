(** * Various tactics for dealing with charge logics and separation logics. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.common_tactics.
Require Import x86proved.charge.ilogic x86proved.charge.sepalg x86proved.charge.bilogic x86proved.charge.later x86proved.charge.csetoid.
Require Import x86proved.spec.
Require Import x86proved.charge.iltac.
Require Import Coq.Setoids.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Generalizable All Variables.

(** Like [split], but for ilogic *)
Ltac ilsplit :=
  (** First match the goal with the appropriate form, to get nice error messages *)
  match goal with
    | [ |- ?A |-- ?B //\\ ?C ] => idtac
    | [ |- ?A |-- ?B ] => fail 0 "Conclusion" B "is not of the form _ //\\ _"
    | [ |- ?G ] => fail 0 "Goal" G " is not of the form _ |-- _ //\\ _"
  end;
  apply landR.

(** Like [assumption], except for ilogic, and use the given [unify] tactic for finding the right hypothesis *)
Ltac ilassumption_with unify :=
  (** Make this a proper tactic, not something returning a tactic (the [match] should not be immediate *)
  idtac;
  match goal with
    | [ |- ?A |-- ?B ] => unify A B; reflexivity
    | [ |- ?A //\\ ?B |-- ?C ] => apply landL1; ilassumption_with unify
    | [ |- ?A //\\ ?B |-- ?C ] => apply landL2; ilassumption_with unify
    | [ |- ?A |-- ?B ] => fail 1 "No assumption matching" B "in" A
    | [ |- ?G ] => fail 1 "Goal" G "is not of the form ? |-- ?"
  end.

Ltac ilassumption := ilassumption_with ltac:(fun x y => unify x y).

(** Like [intro] but for ilogic *)
Ltac ilintro :=
  match goal with
    | [ |- ?A |-- ?B -->> ?C ] => idtac
    | [ |- ?A |-- ?B ] => fail 0 "Conclusion" B "is not of the form _ -->> _"
    | [ |- ?G ] => fail 0 "Goal" G " is not of the form _ |-- _ -->> _"
  end;
  apply limplAdj.

Ltac ilintros := do ?ilintro.

(** Look for an implication in the hypothesis list of an ilogic term [G] whose conclusion matches [concl] *)
Ltac general_find_impl_with_concl G concl :=
  match G with
    | concl => constr:(G)
    | ?A -->> ?B => let test := general_find_impl_with_concl B concl in constr:(G)
    | ?A //\\ ?B => general_find_impl_with_concl A concl
    | ?A //\\ ?B => general_find_impl_with_concl B concl
    | _ => fail 1 "Statement" G "does not contain an implication ending with" concl
  end.
(** Look for an implication in the hypothesis list of an ilogic term [G] whose conclusion matches [concl], and which only has one assumption *)
Ltac find_impl_with_concl G concl :=
  match G with
    | ?A -->> concl => constr:(G)
    | ?A //\\ ?B => find_impl_with_concl A concl
    | ?A //\\ ?B => find_impl_with_concl B concl
    | _ => fail 1 "Statement" G "does not contain an implication of the form _ -->>" concl
  end.
(** Find an implication in the hypothesis list that can be applied *)
Ltac find_impl_to_apply :=
  let hyps := match goal with |- ?hyps |-- ?concl => constr:(hyps) end in
  let concl := match goal with |- ?hyps |-- ?concl => constr:(concl) end in
  find_impl_with_concl hyps concl.

(** like [move hyp at top] and [move hyp at bottom], except matches on
    type rather than name and is for ilogic *)
Tactic Notation "ilmove" open_constr(hyp) "at" "bottom" :=
  do ?[ rewrite -> !(landC hyp) | rewrite -> !landA ].
Tactic Notation "ilmove" open_constr(hyp) "at" "top" :=
  do ?[ rewrite <- !(landC hyp) | rewrite <- !landA ].

(** Like [hyp_apply *], but it clears the hypothesis it applies, and
    is for ilogic.  Used to progress on goals like [... //\\ (A -->>
    B) //\\ .. |-- B] *)
Ltac ilhyp_consume_apply :=
  let impl := find_impl_to_apply in
  ilmove impl at top;
    rewrite -> ?landA;
    match goal with
      | [ |- ?A |-- ?A ] => reflexivity
      | [ |- ?A -->> ?C |-- _ ] => rewrite -> (@landR _ _ _ (A -->> C) ltrue _ (reflexivity _) (ltrueR _))
      | _ => idtac
    end;
    apply limplL; last by ilassumption.

(** Look for a [Forall _, _] in an ilogic term [G] *)
Ltac find_lforall_in G :=
  match G with
    | lforall _ => constr:(G)
    | ?A //\\ ?B => find_lforall_in A
    | ?A //\\ ?B => find_lforall_in B
    | _ => fail 1 "Statement" G "does not contain a Forall _, _"
  end.
(** Find a [Forall _, _] in the hypothesis list *)
Ltac find_lforall :=
  let hyps := match goal with |- ?hyps |-- ?concl => constr:(hyps) end in
  find_lforall_in hyps.

Lemma land_lforallL {Frm ILOps'} `{@ILogic Frm ILOps'} {T} x (P : T -> Frm) (A C : Frm)
: P x //\\ A |-- C -> (Forall x, P x) //\\ A |-- C.
Proof.
  move => H'.
  rewrite <- H'.
  ilsplit; last by ilassumption.
  apply landL1.
  eapply lforallL; reflexivity.
Qed.

(** [specialize] a hypothesis of a given type with an evar. *)
Ltac ilespecialize type :=
  ilmove type at top;
  rewrite -> ?landA;
  match type with
    | lforall _ => idtac
    | _ => fail 1 "The given hypothesis type" type "is not of the form Forall _, _"
  end;
  (lazymatch goal with
     | [ |- _ //\\ _ |-- _ ] => eapply land_lforallL
     | [ |- _ |-- _ ] => eapply lforallL
     | [ |- ?G ] => fail "Goal" G "is not of the form _ |-- _"
   end).

Tactic Notation "ilespecialize" open_constr(type) := ilespecialize type.
Tactic Notation "ilespecialize" "*" :=
  let type := find_lforall in
  ilespecialize type.

Lemma strip_andL_impl {Frm ILOps'} `{@ILogic Frm ILOps'}
      {A B C B' C'}
: @lentails Frm ILOps' (B -->> C) (B' -->> C')
  -> @lentails Frm ILOps' (A //\\ B -->> C) (A //\\ B' -->> C').
Proof.
  move => H'.
  apply landAdj in H'.
  rewrite <- H'; clear H'.
  do ![ ilsplit | ilassumption | ilintro | ilhyp_consume_apply ].
Qed.

Ltac simpl_logic' :=
  idtac;
  match goal with
    | [ |- appcontext[?x == ?x] ] => rewrite (eq_refl x)
    | [ |- ltrue //\\ _ |-- _ ] => apply: landL2
    | [ |- _ //\\ ltrue |-- _ ] => apply: landL1
    | [ |- _ |-- ltrue ] => apply ltrueR
    | [ |- _ |-- _ -->> _ ] => apply: limplAdj
    | [ |- _ /\ _ ] => split
    | [ |- |>?a |-- |>?b ] => f_cancel; []
    | [ |- ?a @ ?b |-- ?a @ ?b' ] => f_cancel; []
    | [ |- ?a <@ ?b |-- ?a' <@ ?b ] => f_cancel; []
    | [ |- ?a <@ ?b |-- ?a <@ ?b' ] => f_cancel; []
    | [ |- ?P //\\ ?Q |-- ?P ] => apply: (@landL1 _ _ _ P Q P (reflexivity _))
    | [ |- ?Q //\\ ?P |-- ?P ] => apply: (@landL2 _ _ _ Q P P (reflexivity _))
    | [ |- context[_ @ empSP] ] => rewrite -> empSPL
    | [ |- context[_ ** empSP] ] => rewrite -> empSPR
    | [ |- context[empSP ** _] ] => rewrite -> empSPL
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
    | _ => syntax_unify_reflexivity
  end.
Ltac finish_logic_with tac := do ?[ finish_logic_with' tac
                                  | idtac;
                                    match goal with
                                      | [ |- _ //\\ _ |-- _ ] => apply landL1; by finish_logic_with tac
                                      | [ |- _ //\\ _ |-- _ ] => apply landL2; by finish_logic_with tac
                                      | _ => ilespecialize *; (** save evars for later *) last first; by finish_logic_with tac
                                    end ].
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

Lemma triple_limpl' `{@ILogic Frm ILOps'} (A B C : Frm) :  A -->> B -->> C |-- ((A -->> B) -->> A -->> C).
Proof.
  repeat match goal with
           | _ => progress simpl_logic
           | [ |- (?A //\\ ?B) //\\ ?C |-- _ ] => rewrite (landA A B C)
           | [ |- (_ -->> _) //\\ _ |-- _ ] => eapply limplL; first by simpl_logic
           | [ |- ?A //\\ (?B //\\ ?C) |-- _ ] => rewrite <- (landA A B C), (landC A B), -> (landA B A C); eapply limplL; first by simpl_logic
         end.
Qed.

Ltac lrevert x :=
  revert x;
  let T := match goal with |- forall H0 : ?T, _ |-- @?P H0 => constr:(T) end in
  let P := match goal with |- forall H0 : ?T, _ |-- @?P H0 => constr:(P) end in
  intro x;
    setoid_rewrite <- (@lforallL _ _ _ T x P _ (reflexivity _));
    try clear x.

Lemma lforall_limpl_commute `{@ILogic Frm ILOps'} {A P Q}
: Forall (x : A), P -->> Q x -|- P -->> Forall (x : A), Q x.
Proof.
  repeat match goal with
           | [ H : _ |- _ ] => progress lforallL H
           | _ => progress lforallR => ?
           | _ => progress finish_logic
           | _ => syntax_unify_reflexivity
         end.
Qed.

(** TODO(t-jagro): Figure out if this already exists somewhere *)
Lemma lentails_def1  `{@ILogic Frm ILOps'} P Q (H' : forall C, C |-- P -> C |-- Q) : P |-- Q.
Proof.
  rewrite <- H'; reflexivity.
Qed.
