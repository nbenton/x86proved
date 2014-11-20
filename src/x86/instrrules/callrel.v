(** * CALL (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [not] and [goal_has_evar] *).
Require Import x86proved.basicspectac (* for [specapply *] *).
Require Import x86proved.chargetac (* for [finish_logic] *).

Require Import x86proved.x86.addr.

Lemma CALLrel_rule (p q: ADDR) (tgt: JmpTgt AdSize8) (sp:ADDR) (w:ADDR) O :
  |-- specAtJmpTgt tgt q (fun p' =>
      (
         obs O @ (UIP ~= p' ** USP ~= sp-#8 ** (sp-#8) :-> q) -->>
         obs O @ (UIP ~= p  ** USP ~= sp    ** (sp-#8) :-> w)
    ) <@ (p -- q :-> CALLrel _ tgt)).
Proof. destruct tgt; do_instrrule_triple. Qed.

Lemma CALLrel_loopy_rule (p q: ADDR) (tgt: JmpTgt AdSize8) (w sp:ADDR) (O : PointedOPred) :
  |-- specAtJmpTgt tgt q (fun p' =>
      (
      |> obs O @ (UIP ~= p' ** USP~=sp-#8 ** sp-#8 :-> q) -->>
         obs O @ (UIP ~= p  ** USP~=sp    ** sp-#8 :-> w)
    ) <@ (p -- q :-> CALLrel _ tgt)).
Proof. destruct tgt; do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall tgt : JmpTgt AdSize8, instrrule (CALLrel _ tgt) := fun tgt p q => @CALLrel_rule p q tgt.
Global Instance: forall tgt : JmpTgt AdSize8, loopy_instrrule (CALLrel _ tgt) := fun tgt p q => @CALLrel_loopy_rule p q tgt.

Section specapply_hint.
Local Hint Unfold specAtJmpTgt : specapply.

Corollary CALLrel_R_rule (r:GPReg64) (p q: ADDR) :
  |-- Forall O (w sp: ADDR) p', (
         obs O @ (UIP ~= p' ** r~=p' ** USP~=sp-#8 ** sp-#8 :-> q) -->>
         obs O @ (UIP ~= p  ** r~=p' ** USP~=sp    ** sp-#8 :-> w)
    ) <@ (p -- q :-> CALLrel AdSize8 (JmpTgtRegMem AdSize8 r)).
Proof. specintros => *. specapply *; finish_logic_with sbazooka. Qed.

Corollary CALLrel_R_loopy_rule (r:GPReg64) (p q: ADDR) :
  |-- Forall (O : PointedOPred) (w sp: ADDR) p', (
      |> obs O @ (UIP ~= p' ** r~=p' ** USP~=sp-#8 ** sp-#8 :-> q) -->>
         obs O @ (UIP ~= p  ** r~=p' ** USP~=sp    ** sp-#8 :-> w)
    ) <@ (p -- q :-> CALLrel _ (JmpTgtRegMem AdSize8 r)).
Proof. specintros => *. loopy_specapply *; finish_logic_with sbazooka. Qed.

Corollary CALLrel_I_rule (rel: QWORD) (p q: ADDR) :
  |-- Forall O (w sp: ADDR), (
         obs O @ (UIP ~= addB q rel ** RSP~=sp-#8 ** sp-#8 :-> q) -->>
         obs O @ (UIP ~= p          ** RSP~=sp    ** sp-#8 :-> w)
    ) <@ (p -- q :-> CALLrel AdSize8 (JmpTgtI AdSize8 (mkTgt AdSize8 rel))).
Proof. specintros => *. specapply *; finish_logic_with sbazooka. Qed.

Corollary CALLrel_I_loopy_rule (rel: QWORD) (p q: ADDR) :
  |-- Forall (O : PointedOPred) (w sp: ADDR), (
      |> obs O @ (UIP ~= addB q rel ** USP~=sp-#8 ** sp-#8 :-> q) -->>
         obs O @ (UIP ~= p          ** USP~=sp    ** sp-#8 :-> w)
    ) <@ (p -- q :-> CALLrel AdSize8 (mkTgt AdSize8 rel)).
Proof. specintros => *. loopy_specapply *; finish_logic_with sbazooka. Qed.
End specapply_hint.
