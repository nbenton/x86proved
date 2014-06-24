(** * CALL (rel) instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import safe (* for [safe] *) spectac (* for [specapply] *).

Lemma CALLrel_rule (p q: DWORD) (tgt: JmpTgt) (w sp:DWORD) :
  |-- interpJmpTgt tgt q (fun P p' =>
      (
      |> safe @ (EIP ~= p' ** P ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** P ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel tgt)).
Proof.
  rewrite /interpJmpTgt/interpMemSpecSrc.
  do_instrrule
    ((try specintros => *; autorewrite with push_at);
     apply TRIPLE_safe => ?;
     do !instrrule_triple_bazooka_step idtac).
Qed.

Section specapply_hint.
Local Hint Unfold interpJmpTgt : specapply.

Corollary CALLrel_R_rule (r:Reg) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, Forall p', (
      |> safe @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof.
  specintros => w sp p'.
  specapply (CALLrel_rule p q (JmpTgtR r)). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.

Corollary CALLrel_I_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, (
      |> safe @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof.
  specintros => w sp.
  specapply (CALLrel_rule p q (JmpTgtI rel)). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.
End specapply_hint.
