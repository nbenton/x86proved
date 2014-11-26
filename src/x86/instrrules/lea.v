(** * LEA instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.x86.eval (* for [computeEA] *).

Require Import common_tactics.
Lemma LEA_ruleSameBase (baseval indexval: ADDR) (disp: DWORD) (r: BaseReg AdSize8) (r1:IxReg AdSize8) sc :
  |-- basic (r ~= baseval ** r1 ~= indexval)
            (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ None (Some r) (Some(r1, sc)) disp))) empOP
            (r ~= computeEA (a:=AdSize8) baseval (Some(indexval,sc)) disp ** r1 ~= indexval).
Proof. do_instrrule_triple. Qed.

Lemma LEA_ruleSameBase32 (baseval indexval: DWORD) (disp:DWORD) (r: BaseReg AdSize4) (r1:IxReg AdSize4) sc :
  |-- basic (r ~= baseval ** r1 ~= indexval)
            (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ None (Some r) (Some(r1, sc)) disp))) empOP
            (r ~= computeEA (a:=AdSize4) baseval (Some(indexval,sc)) disp ** r1 ~= indexval).
Proof. do_instrrule_triple. Qed.

Lemma LEA_rule (old baseval indexval disp: DWORD) (r r': GPReg32) (r1:NonSPReg32) sc :
  |-- basic (r ~= old ** r' ~= baseval ** r1 ~= indexval)
            (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ None (Some (r':BaseReg _)) (Some(r1, sc)) disp))) empOP
            (r ~= computeEA (a:=AdSize4) baseval (Some(indexval,sc)) disp ** r' ~= baseval ** r1 ~= indexval).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (offset : DWORD) (r : GPReg32) (r1 : NonSPReg32) sc,
                   instrrule (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ None (Some (r:BaseReg _)) (Some(r1, sc)) offset))) | 0
  := fun offset r r1 sc v indexval => @LEA_ruleSameBase32 v indexval offset r r1 sc.
Global Instance: forall (offset : DWORD) (r r' : GPReg32) (r1 : NonSPReg32) sc,
                   instrrule (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ None (Some (r':BaseReg _)) (Some(r1, sc)) offset))) | 1
  := fun offset r r' r1 sc old v indexval => @LEA_rule old v indexval offset r r' r1 sc.
