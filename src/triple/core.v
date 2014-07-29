(** * Hoare triples for reasoning about instruction semantics *)
(** This is architecture-neutral, and assumes only a model that
    supports registers, flags and memory. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.bitsops x86proved.bitsopsprops x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.pmapprops x86proved.x86.ioaction.
Require Import x86proved.monad x86proved.monadinst x86proved.reader x86proved.spred x86proved.opred x86proved.spredtotal x86proved.septac x86proved.pointsto x86proved.pfun x86proved.cursor x86proved.writer.
Require Import x86proved.common_tactics x86proved.common_definitions.

Module Import tripleconfig.
  Export Ssreflect.ssreflect  Ssreflect.ssrfun Ssreflect.ssrbool (* for [==] notation *) Ssreflect.ssrnat (* for getting levels right *) Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq (* for [++] *) Ssreflect.fintype.
  Export x86proved.x86.procstate (* for [ProcState] *) (*x86proved.x86.procstatemonad (* for [ST] *)*).
  Export x86proved.spred (* for [SPred], [lentails] *) x86proved.opred (* for [OPred] *) x86proved.spredtotal (* for coercion [ProcState >-> PState] *).
  Export x86proved.monad (* for [bind] and [retn] *).

  Global Set Implicit Arguments.
  Global Unset Strict Implicit.
End tripleconfig.

Import Prenex Implicits.

(** Hoare triple for machine state monad *)
(** We ocassionally talk about the return value *)
Definition valued_TRIPLE {T} (v : T) (P:SPred) (c:ST T) (O:OPred) (Q:SPred) :=
  forall (s:ProcState), P s ->
    exists f o, c s = (o, (f, Success _ v)) /\ O (outputToActions o) /\ Q f.
Notation TRIPLE := (@valued_TRIPLE unit tt).

(** The general rule for dealing with [TRIPLE] by computation *)
Lemma triple_fin {T} (v : T) (P:SPred) (c:ST T) (O:OPred) (Q:SPred)
      (H : forall (s:ProcState),
             P (toPState s)
             -> let trace := c s in
                let outputs := fst trace in
                let f := fst (snd trace) in
                let ex := snd (snd trace) in
                match ex with
                  | Success v' => v = v' /\ O (outputToActions outputs) /\ Q (toPState f)
                  | Error _ => False
                end)
: valued_TRIPLE v P c O Q.
Proof.
  move => s H'.
  specialize (H s H'); simpl in H; generalize dependent (c s).
  move => *.
  do ![ progress subst
      | progress destruct_head False
      | progress destruct_head errorMT
      | progress destruct_head OutputM
      | progress destruct_head Result
      | progress destruct_head prod
      | progress destruct_head unit
      | progress destruct_head and
      | by do !esplit ].
Qed.

Ltac triple_hnf :=
  let v := match goal with |- valued_TRIPLE ?v ?P ?c ?O ?Q => constr:(v) end in
  let P := match goal with |- valued_TRIPLE ?v ?P ?c ?O ?Q => constr:(P) end in
  let c := match goal with |- valued_TRIPLE ?v ?P ?c ?O ?Q => constr:(c) end in
  let O := match goal with |- valued_TRIPLE ?v ?P ?c ?O ?Q => constr:(O) end in
  let Q := match goal with |- valued_TRIPLE ?v ?P ?c ?O ?Q => constr:(Q) end in
  let c' := hnf_under_binders c in
  change (valued_TRIPLE v P c' O Q).

Ltac triple_post_compute :=
  do ?[ progress (simpl fst; simpl snd)
      | progress cbv iota zeta beta
      | progress hnf_in_match'; progress cbv iota zeta beta
      | progress autorewrite with matchdb
      | progress ssr_autorewrite_with_matchdb' ].

Ltac triple_by_compute :=
  triple_hnf;
  apply triple_fin;
  destruct_head_hnf unit;
  let H := fresh "H" in
  let s := fresh "s" in
  (move => H s);
    triple_post_compute;
    repeat split;
    triple_post_compute;
    try eassumption.
