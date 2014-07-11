(** * JMP (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [evar_safe_reflexivity] *).

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

Section specapply_hint.
Local Hint Unfold interpJmpTgt : specapply.

(** TODO(t-jagro): Move these somewhere better, or, better yet, find a systematic way to do this *)
Local Ltac t_spec_logic' :=
  idtac;
  match goal with
    | [ |- _ |-- _ ] => evar_safe_reflexivity
    | [ |- _ |-- _ ] => progress ssimpl
    | [ |- _ |-- _ <@ _ ] => rewrite <-spec_reads_frame
    | [ |- _ |-- _ -->> _ ] => apply limplValid
    | _ => progress autorewrite with push_at
    | [ |- |>_ @ _ |-- |>_ @ _ ] => cancel1
    | [ |- ?S @ _ |-- ?S @ _ ] => cancel1
  end.

Local Ltac t := try eassumption; do !t_spec_logic'.

Lemma JMPrel_I_rule (rel: DWORD) (p q: DWORD):
  |-- (Forall O,
       (obs O @ (EIP ~= addB q rel)
           -->> obs O @ (EIP ~= p)) <@ (p -- q :-> JMPrel rel)).
Proof.
  specintros => O. specapply (JMPrel_rule rel); t.
Qed.

Lemma JMPrel_I_loopy_rule (rel: DWORD) (p q: DWORD):
  |-- (Forall (O : PointedOPred),
       (|> obs O @ (EIP ~= addB q rel)
           -->> obs O @ (EIP ~= p)) <@ (p -- q :-> JMPrel rel)).
Proof.
  specintros => O. specapply (JMPrel_loopy_rule rel); t.
Qed.

Lemma JMPrel_R_rule (r:Reg) (addr: DWORD) (p q: DWORD) :
  |-- (Forall O,
       (obs O @ (EIP ~= addr ** r ~= addr)
           -->> obs O @ (EIP ~= p ** r ~= addr)) <@ (p -- q :-> JMPrel r)).
Proof.
  specintros => O. specapply (JMPrel_rule r); t.
Qed.

Lemma JMPrel_R_loopy_rule (r:Reg) (addr: DWORD) (p q: DWORD) :
  |-- (Forall (O : PointedOPred),
       (|> obs O @ (EIP ~= addr ** r ~= addr)
           -->> obs O @ (EIP ~= p ** r ~= addr)) <@ (p -- q :-> JMPrel r)).
Proof.
  specintros => O. specapply (JMPrel_loopy_rule r); t.
Qed.
End specapply_hint.
