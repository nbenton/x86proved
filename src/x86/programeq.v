Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.choice Ssreflect.seq.
Require Import Ssreflect.generic_quotient.
Require Import x86proved.x86.program x86proved.x86.instr.

Local Open Scope quotient_scope.

(**

 * Equality of [program]s is defined by [progEq], which captures the
 * monoidal sequencing of operations (unit: [prog_skip], composition:
 * [prog_seq]) (and scope extrusion, not treated here).
 *
 * This module quotients away these identities by reflecting [program]
 * onto the [program -> program] function space: identity is thus
 * (function) identity and composition is then (function) composition.
 *
 * Through lemma [program_equal], we can reduce the problem of
 * deciding whether two programs [p1] and [p2] are equivalent by
 * comparing there normal forms.
 *
 *)

(* TODO: retrofit into http://perso.crans.org/cohen/work/quotients/? *)

Fixpoint quote (p: program): program -> program :=
  match p with
  | prog_instr c => fun p => prog_instr c ;; p
  | prog_skip => fun p => p
  | prog_seq p1 p2 =>
    fun p => quote p1 (quote p2 p)
  | prog_declabel body =>
    fun p => prog_declabel body ;; p
  | prog_label l =>
    fun p => prog_label l ;; p
  | prog_data T R W RT v =>
    fun p => prog_data RT v ;; p
  end.

Definition reify (q: program -> program): program :=
  q prog_skip.

Definition norm (p: program): program := reify (quote p).

Lemma quote_hom (p: program)(xs : program) : progEq (quote p xs) (p ;; xs).
Proof.
  elim: p xs.
  * (* CASE: p ~ prog_instr c *)
    by move=> c xs;
       apply progEqRefl.
  * (* CASE: p ~ prog_skip *)
    by move=> xs;
       apply progEqSym ;
       apply progEqSkipSeq.
  * (* CASE: p ~ prog_seq p1 p2 *)
    move=> p1 IH1 p2 IH2 xs /=.
    apply progEqTrans with (p2 := (p1;; p2;; xs));
      last by apply progEqSeqAssoc.
    apply progEqTrans with (p2 := p1 ;; quote p2 xs).
    - by apply IH1 with (xs := quote p2 xs).
    - apply progEqSeq; first by apply progEqRefl.
      by apply IH2 with (xs := xs).
  * (* CASE: p ~ prog_declabel body *)
    by move=> body IH1 xs /=;
       apply progEqRefl.
  * (* CASE: p ~ prog_label l *)
    by move=> l xs /=;
       apply progEqRefl.
  * (* CASE: p ~ prog_data RT v *)
    by move=> T R W RT v xs /=;
       apply progEqRefl.
Qed.

Lemma soundness (p: program): progEq (norm p) p.
Proof.
  apply progEqTrans with (p2 := p ;; prog_skip);
    last by apply progEqSeqSkip.
  apply: quote_hom.
Qed.

Lemma program_equal (p1 p2: program):
  progEq (norm p1) (norm p2) -> progEq p1 p2.
Proof.
  move=> H.
  apply progEqTrans with (p2 := norm p1);
    first by apply progEqSym;
             apply soundness.
  apply progEqTrans with (p2 := norm p2);
    first by exact: H.
  apply soundness.
Qed.
