(** * JMP (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [evar_safe_reflexivity] *).
Require Import x86proved.basicspectac (* for [specapply *] *).
Require Import x86proved.chargetac (* for [finish_logic] *).

Lemma JMPrel_rule (tgt: JmpTgt AdSize8) (p q: ADDR)
: |-- specAtJmpTgt tgt q (fun addr =>
                            (Forall O,
                             (obs O @ (UIP ~= addr)
                         -->> obs O @ (UIP ~= p)) <@ (p -- q :-> JMPrel _ tgt))).
Proof. destruct tgt; do_instrrule_triple. Qed. 

Lemma JMPrel_loopy_rule (tgt: JmpTgt AdSize8 ) (p q: ADDR)
: |-- specAtJmpTgt tgt q (fun addr =>
                            (Forall (O : PointedOPred),
                             (|> obs O @ (UIP ~= addr)
                                 -->> obs O @ (UIP ~= p)) <@ (p -- q :-> JMPrel _ tgt))).
Proof. destruct tgt; do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (tgt : JmpTgt _), instrrule (JMPrel _ tgt) := @JMPrel_rule.
Global Instance: forall (tgt : JmpTgt _), loopy_instrrule (JMPrel _ tgt) := @JMPrel_loopy_rule.

Section specapply_hint.
Local Hint Unfold specAtJmpTgt : specapply.

Lemma JMPrel_I_rule (rel: QWORD) (p q: ADDR):
  |-- (Forall O,
       (obs O @ (UIP ~= addB q rel)
           -->> obs O @ (UIP ~= p)) <@ (p -- q :-> JMPrel AdSize8 (mkTgt AdSize8 rel))).
Proof. specintros => *. specapply *; finish_logic_with sbazooka. Qed.

Lemma JMPrel_I_loopy_rule (rel: QWORD) (p q: ADDR):
  |-- (Forall (O : PointedOPred),
       (|> obs O @ (UIP ~= addB q rel)
           -->> obs O @ (UIP ~= p)) <@ (p -- q :-> JMPrel _ (mkTgt AdSize8 rel))).
Proof. specintros => *. loopy_specapply *; finish_logic_with sbazooka. Qed.

Lemma JMPrel_R_rule (r:GPReg64) (addr: ADDR) (p q: ADDR) :
  |-- (Forall O,
       (obs O @ (UIP ~= addr ** r ~= addr)
           -->> obs O @ (UIP ~= p ** r ~= addr)) <@ (p -- q :-> JMPrel _ (JmpTgtRegMem AdSize8 (RegMemR _ r)))).
Proof. specintros => *. specapply *; finish_logic_with sbazooka. Qed.

Lemma JMPrel_R_loopy_rule (r:GPReg64) (addr: ADDR) (p q: ADDR) :
  |-- (Forall (O : PointedOPred),
       (|> obs O @ (UIP ~= addr ** r ~= addr)
           -->> obs O @ (UIP ~= p ** r ~= addr)) <@ (p -- q :-> JMPrel _ (JmpTgtRegMem AdSize8 (RegMemR _ r)))).
Proof. specintros => *. loopy_specapply *; finish_logic_with sbazooka. Qed.
End specapply_hint.
