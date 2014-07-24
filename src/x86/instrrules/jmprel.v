(** * JMP (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [evar_safe_reflexivity] *).
Require Import x86proved.basicspectac (* for [specapply *] *).
Require Import x86proved.chargetac (* for [finish_logic] *).

Lemma JMPrel_rule (tgt: JmpTgt) (p q: DWORD)
: |-- interpJmpTgt tgt q (fun P addr =>
                            (Forall O,
                             (obs O @ (EIP ~= addr ** P)
                                 -->> obs O @ (EIP ~= p ** P)) <@ (p -- q :-> JMPrel tgt))).
Proof.
  rewrite /interpJmpTgt/interpMemSpecSrc.
  do_instrrule
    ((try specintros => *; autorewrite with push_at);
     apply: TRIPLE_safe => ?;
     do !instrrule_triple_bazooka_step idtac).
Qed.

Lemma JMPrel_loopy_rule (tgt: JmpTgt) (p q: DWORD)
: |-- interpJmpTgt tgt q (fun P addr =>
                            (Forall (O : PointedOPred),
                             (|> obs O @ (EIP ~= addr ** P)
                                 -->> obs O @ (EIP ~= p ** P)) <@ (p -- q :-> JMPrel tgt))).
Proof.
  rewrite /interpJmpTgt/interpMemSpecSrc.
  do_instrrule
    ((try specintros => *; autorewrite with push_at);
     apply: TRIPLE_safeLater => ?;
     do !instrrule_triple_bazooka_step idtac).
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (tgt : JmpTgt), instrrule (JMPrel tgt) := @JMPrel_rule.
Global Instance: forall (tgt : JmpTgt), loopy_instrrule (JMPrel tgt) := @JMPrel_loopy_rule.

Section specapply_hint.
Local Hint Unfold interpJmpTgt : specapply.

Lemma JMPrel_I_rule (rel: DWORD) (p q: DWORD):
  |-- (Forall O,
       (obs O @ (EIP ~= addB q rel)
           -->> obs O @ (EIP ~= p)) <@ (p -- q :-> JMPrel rel)).
Proof. specintros => *. specapply *; finish_logic_with sbazooka. Qed.

Lemma JMPrel_I_loopy_rule (rel: DWORD) (p q: DWORD):
  |-- (Forall (O : PointedOPred),
       (|> obs O @ (EIP ~= addB q rel)
           -->> obs O @ (EIP ~= p)) <@ (p -- q :-> JMPrel rel)).
Proof. specintros => *. loopy_specapply *; finish_logic_with sbazooka. Qed.

Lemma JMPrel_R_rule (r:Reg) (addr: DWORD) (p q: DWORD) :
  |-- (Forall O,
       (obs O @ (EIP ~= addr ** r ~= addr)
           -->> obs O @ (EIP ~= p ** r ~= addr)) <@ (p -- q :-> JMPrel r)).
Proof. specintros => *. specapply *; finish_logic_with sbazooka. Qed.

Lemma JMPrel_R_loopy_rule (r:Reg) (addr: DWORD) (p q: DWORD) :
  |-- (Forall (O : PointedOPred),
       (|> obs O @ (EIP ~= addr ** r ~= addr)
           -->> obs O @ (EIP ~= p ** r ~= addr)) <@ (p -- q :-> JMPrel r)).
Proof. specintros => *. loopy_specapply *; finish_logic_with sbazooka. Qed.
End specapply_hint.
