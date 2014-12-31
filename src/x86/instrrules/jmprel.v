(** * JMP (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [evar_safe_reflexivity] *).
Require Import x86proved.basicspectac (* for [specapply *] *).
Require Import x86proved.chargetac (* for [finish_logic] *).

Lemma JMPrel_rule (tgt: JmpTgt AdSize8) (p q: ADDR) 
: |-- specAtJmpTgt tgt q (fun addr =>
                            ((|> safe  @ (UIP ~= addr)
                            -->> safe @ (UIP ~= p)) c@ (p -- q :-> JMPrel _ tgt))).
Proof.
  rewrite /specAtJmpTgt/specAtMemSpecSrc.
  destruct tgt; do_instrrule_triple.
Qed.

Global Instance: forall (tgt : JmpTgt _), instrrule (JMPrel _ tgt) := @JMPrel_rule.

Section specapply_hint.
Local Hint Unfold specAtJmpTgt : specapply.

Lemma JMPrel_I_rule (rel: QWORD) (p q: ADDR):
  |-- ((|> safe @ (UIP ~= addB q rel)
           -->> safe @ (UIP ~= p)) c@ (p -- q :-> JMPrel AdSize8 (mkTgt AdSize8 rel))).
Proof. superspecapply *. finish_logic. Qed.

Lemma JMPrel_R_rule (r:GPReg64) (addr: ADDR) (p q: ADDR) :
  |-- ((|> safe @ (UIP ~= addr ** r ~= addr)
           -->> safe @ (UIP ~= p ** r ~= addr)) c@ (p -- q :-> JMPrel _ (JmpTgtRegMem AdSize8 (RegMemR _ r)))).
Proof. 
let R := get_next_instrrule_from_eip in have RR:= R. 
eforalls RR. rewrite ->spec_at_swap in RR. 
rewrite -> spec_at_impl in RR. superspecapply RR. 
finish_logic_with sbazooka. Qed.

End specapply_hint.
