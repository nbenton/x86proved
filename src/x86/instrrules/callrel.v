(** * CALL (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).

Lemma CALLrel_rule (p q: DWORD) (tgt: JmpTgt) (w sp:DWORD) O :
  |-- interpJmpTgt tgt q (fun P p' =>
      (
      |> obs O @ (EIP ~= p' ** P ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** P ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel tgt)).
Proof.
  rewrite /interpJmpTgt/interpMemSpecSrc.
  do_instrrule
    ((try specintros => *; autorewrite with push_at);
     apply TRIPLE_safeLater => ?;
     do !instrrule_triple_bazooka_step idtac).
Qed.

Section specapply_hint.
Local Hint Unfold interpJmpTgt : specapply.

Corollary CALLrel_R_rule (r:Reg) (p q: DWORD) :
  |-- Forall O, Forall w: DWORD, Forall sp:DWORD, Forall p', (
      |> obs O @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof.
  specintros => O w sp p'.
  specapply (CALLrel_rule p q r). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.

Corollary CALLrel_I_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall O, Forall w: DWORD, Forall sp:DWORD, (
      |> obs O @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p          ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof.
  specintros => O w sp.
  specapply (CALLrel_rule p q rel). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.
End specapply_hint.
