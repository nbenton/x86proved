(** * CALL (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [not] and [goal_has_evar] *).
Require Import x86proved.basicspectac (* for [specapply *] *).
Require Import x86proved.chargetac (* for [finish_logic] *).

Require Import x86proved.x86.addr.

Lemma CALLrel_rule (p q: ADDR) (tgt: JmpTgt AdSize8) (w sp:ADDR):
  |-- specAtJmpTgt tgt q (fun p' =>
      (
      |> safe @ (UIP ~= p' ** USP~=sp-#8 ** sp-#8 :-> q) -->>
         safe @ (UIP ~= p  ** USP~=sp    ** sp-#8 :-> w)
    ) c@ (p -- q :-> CALLrel _ tgt)).
Proof. 
  rewrite /specAtJmpTgt/specAtMemSpecSrc.
  destruct tgt; do_instrrule_triple. 
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall tgt : JmpTgt AdSize8, instrrule (CALLrel _ tgt) := fun tgt p q => @CALLrel_rule p q tgt.

Section specapply_hint.
Local Hint Unfold specAtJmpTgt : specapply.

Corollary CALLrel_R_rule (r:GPReg64) (p q: ADDR) :
  |-- Forall (w sp: ADDR) p', (
      |> safe @ (UIP ~= p' ** r~=p' ** USP~=sp-#8 ** sp-#8 :-> q) -->>
         safe @ (UIP ~= p  ** r~=p' ** USP~=sp    ** sp-#8 :-> w)
    ) c@ (p -- q :-> CALLrel AdSize8 (JmpTgtRegMem AdSize8 r)).
Proof. specintros => *. 
let R := get_next_instrrule_from_eip in have RR:= R. 
eforalls RR. rewrite ->spec_at_swap in RR. 
rewrite -> spec_at_impl in RR. superspecapply RR. 
finish_logic_with sbazooka. Qed.

Corollary CALLrel_I_rule (rel: QWORD) (p q: ADDR) :
  |-- Forall (w sp: ADDR), (
      |> safe @ (UIP ~= addB q rel ** USP~=sp-#8 ** sp-#8 :-> q) -->>
         safe @ (UIP ~= p          ** USP~=sp    ** sp-#8 :-> w)
    ) c@ (p -- q :-> CALLrel AdSize8 (mkTgt AdSize8 rel)).
Proof. specintros => *. superspecapply *. finish_logic_with sbazooka. Qed.
End specapply_hint.
