(** * CALL (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [not] and [goal_has_evar] *).
Require Import x86proved.basicspectac (* for [specapply *] *).
Require Import x86proved.chargetac (* for [finish_logic] *).

Lemma CALLrel_rule (p q: DWORD) (tgt: JmpTgt) (w sp:DWORD):
  |-- interpJmpTgt tgt q (fun P p' =>
      (
      |> safe @ (EIP ~= p' ** P ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** P ** ESP~=sp    ** sp-#4 :-> w)
    ) @ (p -- q :-> CALLrel tgt)).
Proof.
  rewrite /interpJmpTgt/interpMemSpecSrc.
  do_instrrule
    (try specintros => *;
     apply: TRIPLE_safeLater => ?;
     do !instrrule_triple_bazooka_step idtac).
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall tgt : JmpTgt, instrrule (CALLrel tgt) := fun tgt p q => @CALLrel_rule p q tgt.

Section specapply_hint.
Local Hint Unfold interpJmpTgt : specapply.

Corollary CALLrel_R_rule (r:Reg) (p q: DWORD) :
  |-- Forall (w sp: DWORD) p', (
      |> safe @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) @ (p -- q :-> CALLrel r).
Proof. specintros => *. superspecapply *. finish_logic_with sbazooka. Qed.

Corollary CALLrel_I_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall (w sp: DWORD), (
      |> safe @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p          ** ESP~=sp    ** sp-#4 :-> w)
    ) @ (p -- q :-> CALLrel rel).
Proof. specintros => *. superspecapply *. finish_logic_with sbazooka. Qed.
End specapply_hint.
