(*===========================================================================
  Auxiliary lemmas for Hoare triples on *programs*
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.opred x86proved.septac x86proved.spec x86proved.spectac x86proved.obs x86proved.pointsto x86proved.cursor x86proved.x86.instr x86proved.reader x86proved.x86.instrcodec.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import x86proved.x86.program x86proved.x86.basic x86proved.charge.ilogic.
Require Import x86proved.common_tactics.

(* Morphism for program equivalence *)
Global Instance basic_progEq_m {T_OPred} {proj} :
Proper (lequiv ==> progEq ==> lequiv ==> lequiv ==> lequiv) (@parameterized_basic T_OPred proj _ _).
  Proof.
    move => P P' HP c c' Hc O O' HO Q Q' HQ. split.
    setoid_rewrite -> HQ. setoid_rewrite HP. setoid_rewrite HO.
    unfold parameterized_basic. by setoid_rewrite Hc.
    setoid_rewrite <- HQ. setoid_rewrite <- HP. setoid_rewrite <- HO.
    unfold parameterized_basic. by setoid_rewrite <-Hc.
  Qed.

(* Skip rule *)
Lemma basic_skip {T_OPred} {proj} P: |-- @parameterized_basic T_OPred proj _ _ P prog_skip empOP P.
Proof.
  rewrite /parameterized_basic. specintros => i j O'. unfold_program.
  specintro => ->.
  rewrite -> empOPL. rewrite emp_unit spec_reads_eq_at; rewrite <- emp_unit.
  rewrite spec_at_emp. by apply limplValid.
Qed.

(* Sequencing rule *)
Lemma basic_seq_helper {T_OPred} {proj} mkCatOP (c1 c2: program) S P O1 Q (O2 : T_OPred) R O:
  (forall O', proj (mkCatOP O2 O') -|- catOP (proj O2) (proj O')) ->
  catOP O1 (proj O2) |-- O ->
  S |-- @parameterized_basic T_OPred proj _ _ P c1 O1 Q ->
  S |-- @parameterized_basic T_OPred proj _ _ Q c2 (proj O2) R ->
  S |-- @parameterized_basic T_OPred proj _ _ P (c1;; c2) O R.
Proof.
  rewrite /parameterized_basic.
  move=> HcO' HO Hc1 Hc2.
  unfold lequiv in HcO'. split_and. specintros => i j O'. unfold_program.
  specintro => i'. rewrite -> memIsNonTop. specintros => p' EQ.
  rewrite <- HO. rewrite -> catOPA.
  eforalls Hc1.
  eforalls Hc2.
  repeat match goal with
           | [ H : ?SH |-- (?AH -->> obs ?OH @ ?BH) <@ ?FH |- ?S |-- (?A -->> obs ?O @ ?B) <@ ?F ]
             => syntax_unify SH S;
               syntax_unify BH B;
               specapply H; try (by ssimpl); try (by f_cancel); []
           | _ => progress rewrite spec_at_emp
         end.
  repeat match goal with
           | _ => evar_safe_reflexivity
           | [ |- _ |-- (?a -->> ?a) <@ _ ] => rewrite <- spec_reads_frame
           | [ |- _ |-- ?a -->> ?a ] => apply: limplAdj
           | [ |- _ //\\ ?a |-- ?a ] => apply: landL2
           | [ |- ?a //\\ _ |-- ?a ] => apply: landL1
           | [ |- _ //\\ ?a |-- ?a ] => apply: landL2
         end.
Qed.

Definition basic_seq (c1 c2: program) S P O1 Q (O2 : OPred) R O
: catOP O1 O2 |-- O ->
  S |-- basic P c1 O1 Q ->
  S |-- basic Q c2 O2 R ->
  S |-- basic P (c1;; c2) O R
  := @basic_seq_helper OPred id catOP c1 c2 S P O1 Q O2 R O (fun _ => reflexivity _).

Definition loopy_basic_seq (c1 c2: program) S P O1 Q (O2 : PointedOPred) R O
: catOP O1 O2 |-- O ->
  S |-- loopy_basic P c1 O1 Q ->
  S |-- loopy_basic Q c2 O2 R ->
  S |-- loopy_basic P (c1;; c2) O R
  := @basic_seq_helper PointedOPred OPred_pred (fun O1 O2 => mkPointedOPred (catOP O1 O2) _) c1 c2 S P O1 Q O2 R O (fun _ => reflexivity _).

(* Scoped label rule *)
Lemma basic_local {T_OPred} {proj} S P c O Q:
  (forall l, S |-- @parameterized_basic T_OPred proj _ _ P (c l) O Q) ->
  S |-- @parameterized_basic T_OPred proj _ _ P (prog_declabel c) O Q.
Proof.
  move=> H. rewrite /parameterized_basic. rewrite /memIs /=. specintros => i j O' l.
  specialize (H l). lforwardR H.
  - apply lforallL with i. apply lforallL with j. apply lforallL with O'. reflexivity.
  apply H.
Qed.

(* Needed to avoid problems with coercions *)
Lemma basic_instr {T_OPred} {proj} S P i O Q :
  S |-- @parameterized_basic T_OPred proj _ _ P i O Q ->
  S |-- @parameterized_basic T_OPred proj _ _ P (prog_instr i) O Q.
Proof. done. Qed.

(** Get the program out of a goal; useful for looking up which rule to use. *)
(** Do a separate [lazymatch] and [match] to make sure that the correct
    error message rises to the top; [lazymatch] will evaluate to
    either the [fail 1] tactic or a constr, and then the [match] will
    run the error or return the constr.  *)
Ltac get_basic_program_from G :=
  let ret := lazymatch G with
               | _ |-- ?G' => get_basic_program_from G'
               | parameterized_basic _ ?P _ _ => constr:(P)
               | ?G' => fail 1 "No program found in" G'
             end in
  match True with
    | _ => ret
  end.

Ltac get_first_instr P :=
  lazymatch P with
    | prog_seq ?P' _ => get_first_instr P'
    | prog_instr ?I => constr:(I)
    | ?P' => constr:(P')
  end.

(** A tactic for solving the side conditions when the basicapplied lemma is completely unconstrained. *)
Ltac solve_simple_basicapply :=
  solve [ repeat match goal with
                   | _ => evar_safe_syntax_unify_reflexivity
                   | [ |- _ |-- ltrue ] => solve [ apply ltrueR ]
                   | [ |- lfalse |-- _ ] => solve [ apply lfalseL ]
                   | [ |- ?A |-- ?B ** ?e ] => is_evar e; etransitivity; [ | exact (proj2 (empSPR B)) ]
                   | [ |- ?A ** ?e |-- ?B ] => is_evar e; etransitivity; [ exact (proj1 (empSPR A)) | ]
                   | [ |- ?A |-- ?B ** empSP ] => etransitivity; [ | exact (proj2 (empSPR B)) ]
                   | [ |- ?A ** empSP |-- ?B ] => etransitivity; [ exact (proj1 (empSPR A)) | ]
                   | [ |- ?f ?x |-- ?y ] => is_evar f; atomic x; let T := type_of x in unify f (fun _ : T => y); cbv beta; reflexivity
                   | [ |- ?y |-- ?f ?x ] => is_evar f; atomic x; let T := type_of x in unify f (fun _ : T => y); cbv beta; reflexivity
                   | [ |- ?g (?f ?x) |-- ?g ?y ] => is_evar f; atomic x; let T := type_of x in unify f (fun _ : T => y); cbv beta; reflexivity
                   | [ |- ?g ?y |-- ?g (?f ?x) ] => is_evar f; atomic x; let T := type_of x in unify f (fun _ : T => y); cbv beta; reflexivity
                 end ].

(* Attempts to apply "basic" lemma on a single command (basic_basic) or
   on the first of a sequence (basic_seq). Note that it attempts to use sbazooka
   to discharge subgoals, so be careful if existentials are exposed in the goal --
   they will be instantiated! *)
Hint Unfold not : basicapply.
Hint Rewrite eq_refl : basicapply.
Ltac instRule R H :=
  move: (R) => H;
              repeat (autounfold with basicapply in H);
              eforalls H;
              autorewrite with push_at in H.

(** If our goal is a [loopy_basic] and our lemma is a [basic], then we can weaken the goal. *)
Ltac weaken_parameterized_basic_if_needed Hlem :=
  try (match type_of Hlem with _ |-- basic _ _ _ _ => idtac end;
       apply weaken_parameterized_basic).

(* This is all very sensitive to use of "e" versions of apply/exact. Beware! *)
(* We ensure that we leave at most one goal remaining. *)
Ltac basicatom R tacfin :=
  match goal with
    | |- _ |-- parameterized_basic ?P (prog_instr ?i) ?O ?Q => (eapply basic_basic_context; first eapply basic_instr)
    | _ => eapply basic_basic_context
  end;
  [ weaken_parameterized_basic_if_needed R; eexact R | tacfin .. | try tacfin ].

Ltac basicseq R tacfin :=
  (idtac;
  lazymatch goal with
    | |- _ |-- basic ?P (prog_seq ?p1 ?p2) ?O ?Q => (eapply basic_seq; [ | basicatom R tacfin |]; instantiate; [ try done | .. ])
    | |- _ |-- loopy_basic ?P (prog_seq ?p1 ?p2) ?O ?Q => (eapply loopy_basic_seq; [ | basicatom R tacfin |]; instantiate; [ try done | ..])
    | |- _ |-- @parameterized_basic ?T_OPred ?proj _ _ ?P (prog_seq ?p1 ?p2) ?O ?Q => (eapply (@basic_seq_helper T_OPred proj _) ; [ | | basicatom R tacfin |]; [ | try done | .. ])
    | _ => basicatom R tacfin
  end).

Ltac basicapply_default_tacfin :=
  try solve_simple_basicapply;
  autounfold with spred; sbazooka.

Ltac basicapply_default_hyp_tac Hlem :=
  autorewrite with basicapply in Hlem.

Ltac basicapply R tac tacfin :=
  let Hlem := fresh "Hlem" in
  instRule R Hlem;
    tac Hlem;
    first basicseq Hlem tacfin;
    clear Hlem.

Tactic Notation "basicapply" open_constr(R) "using" tactic3(tac) "side" "conditions" tactic(tacfin) := basicapply R tac tacfin.
Tactic Notation "basicapply" open_constr(R) "using" tactic3(tac) := basicapply R using (tac) side conditions by basicapply_default_tacfin.
Tactic Notation "basicapply" open_constr(R) "side" "conditions" tactic(tacfin) := basicapply R using (basicapply_default_hyp_tac) side conditions tacfin.
Tactic Notation "basicapply" open_constr(R) := basicapply R using basicapply_default_hyp_tac.
(** Variant of [basicapply] that doesn't require that the side conditions be fully solved. *)
Tactic Notation "try_basicapply" open_constr(R) "using" tactic3(tac) := basicapply R using (tac) side conditions basicapply_default_tacfin.
Tactic Notation "try_basicapply" open_constr(R) := try_basicapply R using basicapply_default_hyp_tac.
