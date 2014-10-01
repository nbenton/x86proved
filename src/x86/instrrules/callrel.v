(** * CALL (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [not] and [goal_has_evar] *).
Require Import x86proved.basicspectac (* for [specapply *] *).
Require Import x86proved.chargetac (* for [finish_logic] *).

Lemma CALLrel_rule (p q: ADDR) (tgt: JmpTgt) (sp:ADDR) (w:DWORD) O :
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

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall tgt : JmpTgt, instrrule (CALLrel tgt) := fun tgt p q => @CALLrel_rule p q tgt.
Global Instance: forall tgt : JmpTgt, loopy_instrrule (CALLrel tgt) := fun tgt p q => @CALLrel_loopy_rule p q tgt.

Section specapply_hint.
Local Hint Unfold interpJmpTgt : specapply.

Corollary CALLrel_R_rule (r:GPReg32) (p q: DWORD) :
  |-- Forall O (w sp: DWORD) p', (
         obs O @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof. specintros => *. specapply *; finish_logic_with sbazooka. Qed.

Corollary CALLrel_R_loopy_rule (r:GPReg32) (p q: DWORD) :
  |-- Forall (O : PointedOPred) (w sp: DWORD) p', (
      |> obs O @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof. specintros => *. loopy_specapply *; finish_logic_with sbazooka. Qed.

Corollary CALLrel_I_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall O (w sp: DWORD), (
         obs O @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p          ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof. specintros => *. specapply *; finish_logic_with sbazooka. Qed.

Corollary CALLrel_I_loopy_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall (O : PointedOPred) (w sp: DWORD), (
      |> obs O @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p          ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof. specintros => *. loopy_specapply *; finish_logic_with sbazooka. Qed.
End specapply_hint.
