(** * CALL (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [not] and [goal_has_evar] *).

Lemma CALLrel_rule (p q: DWORD) (tgt: JmpTgt) (w sp:DWORD) O :
  |-- interpJmpTgt tgt q (fun P p' =>
      (
         obs O @ (EIP ~= p' ** P ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** P ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel tgt)).
Proof.
  rewrite /interpJmpTgt/interpMemSpecSrc.
  do_instrrule
    ((try specintros => *; autorewrite with push_at);
     apply: TRIPLE_safe => ?;
     do !instrrule_triple_bazooka_step idtac).
Qed.

Lemma CALLrel_loopy_rule (p q: DWORD) (tgt: JmpTgt) (w sp:DWORD) (O : PointedOPred) :
  |-- interpJmpTgt tgt q (fun P p' =>
      (
      |> obs O @ (EIP ~= p' ** P ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** P ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel tgt)).
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

Corollary CALLrel_R_rule (r:Reg) (p q: DWORD) :
  |-- Forall O (w sp: DWORD) p', (
         obs O @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof.
  specintros => O w sp p'.
  specapply (CALLrel_rule p q r); t.
Qed.

Corollary CALLrel_R_loopy_rule (r:Reg) (p q: DWORD) :
  |-- Forall (O : PointedOPred) (w sp: DWORD) p', (
      |> obs O @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof.
  specintros => O w sp p'.
  specapply (CALLrel_loopy_rule p q r); t.
Qed.

Corollary CALLrel_I_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall O (w sp: DWORD), (
         obs O @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p          ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof.
  specintros => O w sp.
  specapply (CALLrel_rule p q rel); t.
Qed.

Corollary CALLrel_I_loopy_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall (O : PointedOPred) (w sp: DWORD), (
      |> obs O @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p          ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof.
  specintros => O w sp.
  specapply (CALLrel_loopy_rule p q rel); t.
Qed.
End specapply_hint.
