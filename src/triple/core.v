(** * Hoare triples for reasoning about instruction semantics *)
(** This is architecture-neutral, and assumes only a model that
    supports registers, flags and memory. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.bitsops x86proved.bitsopsprops x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.pmapprops x86proved.x86.ioaction.
Require Import x86proved.monad x86proved.monadinst x86proved.reader x86proved.SPred x86proved.OPred x86proved.SPredTotal x86proved.septac x86proved.pointsto x86proved.pfun x86proved.cursor x86proved.writer.
Require Import common_tactics.

Module Import tripleconfig.
  Export Ssreflect.ssreflect  Ssreflect.ssrfun Ssreflect.ssrbool (* for [==] notation *) Ssreflect.ssrnat (* for getting levels right *) Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq (* for [++] *) Ssreflect.fintype.
  Export x86.procstate (* for [ProcState] *) (*x86.procstatemonad (* for [ST] *)*).
  Export SPred (* for [SPred], [lentails] *) OPred (* for [OPred] *) SPredTotal (* for coercion [ProcState >-> PState] *).
  Export x86proved.monad (* for [bind] and [retn] *).

  Global Set Implicit Arguments.
  Global Unset Strict Implicit.
End tripleconfig.

Import Prenex Implicits.

(** Hoare triple for machine state monad *)
Definition TRIPLE (P:SPred) (c:ST unit) (O:OPred) (Q:SPred) :=
  forall s:ProcState, P s ->
    exists f o, c s = (o, Success _ (f,tt)) /\ O (outputToActions o) /\ Q f.

(** The general rule for dealing with [TRIPLE] by computation *)
Lemma triple_fin (P:SPred) (c:ST unit) (O:OPred) (Q:SPred)
      (H : forall s:ProcState,
             P (toPState s)
             -> let outputs := fst (c s) in
                match snd (c s) with
                  | Success ftt =>  O (outputToActions outputs) /\ Q (toPState (fst ftt))
                  | Error _ => False
                end)
: TRIPLE P c O Q.
Proof.
  move => s H'.
  specialize (H s H'); simpl in H; generalize dependent (c s).
  move => *.
  do ![ progress destruct_head False
      | progress destruct_head errorMT
      | progress destruct_head Result
      | progress destruct_head prod
      | progress destruct_head unit
      | progress destruct_head and
      | by do !esplit ].
Qed.

Lemma triple_simple_fin (P:SPred) outputs f (O:OPred) (Q:SPred)
      (H : forall s:ProcState, P (toPState s) -> O (outputToActions (outputs s)) /\ Q (toPState (f s)))
: TRIPLE P (fun s => (outputs s, Success _ (f s, tt))) O Q.
Proof.
  apply triple_fin => s H' /=.
  by apply H.
Qed.

Ltac triple_hnf :=
  let P := match goal with |- TRIPLE ?P ?c ?O ?Q => constr:(P) end in
  let c := match goal with |- TRIPLE ?P ?c ?O ?Q => constr:(c) end in
  let O := match goal with |- TRIPLE ?P ?c ?O ?Q => constr:(O) end in
  let Q := match goal with |- TRIPLE ?P ?c ?O ?Q => constr:(Q) end in
  let c' := hnf_under_binders c in
  change (TRIPLE P c' O Q).

Ltac triple_by_compute :=
  triple_hnf;
  apply triple_fin;
  let H := fresh "H" in
  let s := fresh "s" in
  (move => H s);
    try (split; first by hnf; reflexivity);
    cbv iota zeta;
    simpl fst; simpl snd.
