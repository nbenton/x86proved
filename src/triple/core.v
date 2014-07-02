(** * Hoare triples for reasoning about instruction semantics *)
(** This is architecture-neutral, and assumes only a model that
    supports registers, flags and memory. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.bitsops x86proved.bitsopsprops x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.pmapprops x86proved.x86.ioaction.
Require Import x86proved.monad x86proved.monadinst x86proved.reader x86proved.SPred x86proved.OPred x86proved.SPredTotal x86proved.septac x86proved.pointsto x86proved.pfun x86proved.cursor x86proved.writer.

Module Import tripleconfig.
  Export Ssreflect.ssreflect  Ssreflect.ssrfun Ssreflect.ssrbool (* for [==] notation *) Ssreflect.ssrnat (* for getting levels right *) Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq (* for [++] *) Ssreflect.fintype.
  Export x86.procstate (* for [ProcState] *) (*x86.procstatemonad (* for [ST] *)*).
  Export SPred (* for [SPred], [lentails] *) OPred (* for [OPred] *) SPredTotal (* for coercion [ProcState >-> PState] *).
  Export x86proved.monad (* for [bind] and [retn] *).

  Global Set Implicit Arguments.
  Global Unset Strict Implicit.
End tripleconfig.

Import Prenex Implicits.

(* Hoare triple for machine state monad *)
Definition TRIPLE (P:SPred) (c:ST unit) (O:OPred) (Q:SPred) :=
  forall s:ProcState, P s ->
    exists f o, c s = (o, Success _ (f,tt)) /\ O (outputToActions o) /\ Q f.
