(** * JMP (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).

Lemma JMPrel_rule (tgt: JmpTgt) (p q: DWORD) :
  |-- interpJmpTgt tgt q (fun P addr =>
     Forall O, (|> obs O @ (EIP ~= addr ** P) 
              -->> obs O @ (EIP ~= p ** P)) <@ (p -- q :-> JMPrel tgt)).
Proof.
  rewrite /interpJmpTgt/interpMemSpecSrc.
  do_instrrule
    ((try specintros => *; autorewrite with push_at);
     apply TRIPLE_safeLater => ?;
     do !instrrule_triple_bazooka_step idtac).
Qed.

Section specapply_hint.
Local Hint Unfold interpJmpTgt : specapply.

Lemma JMPrel_I_rule (rel: DWORD) (p q: DWORD):
  |-- Forall O, (|> obs O @ (EIP ~= addB q rel) 
               -->> obs O @ (EIP ~= p)) <@ (p -- q :-> JMPrel rel).
Proof.
  specintros => O. specapply (JMPrel_rule rel). by ssimpl.

  autorewrite with push_at. rewrite <-spec_reads_frame. apply limplValid.
  cancel1. cancel1. sbazooka.
Qed.

Lemma JMPrel_R_rule (r:Reg) (addr: DWORD) (p q: DWORD) :
  |-- Forall O, (|> obs O @ (EIP ~= addr ** r ~= addr) 
               -->> obs O @ (EIP ~= p ** r ~= addr)) <@ (p -- q :-> JMPrel r).
Proof.
  specintros => O. specapply (JMPrel_rule r). by ssimpl.

  rewrite <-spec_reads_frame. autorewrite with push_at. rewrite limplValid.
  cancel1. cancel1. sbazooka.
Qed.
End specapply_hint.
