(** * LEA instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.x86.eval (* for [scaleBy] *).

Lemma LEA_ruleSameBase (v indexval: ADDR) (offset:DWORD) (r: BaseReg AdSize8) (r1:IxReg AdSize8) sc :
  |-- basic (r ~= v ** r1 ~= indexval)
            (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ (Some(mkSIB _ r (Some(r1, sc)))) offset))) empOP
            (r ~= computeIxAddr (a:=AdSize8) v offset (scaleBy sc indexval) ** r1 ~= indexval).
Proof. Admitted. (*do_instrrule_triple. Qed.*)

Lemma LEA_ruleSameBase32 (v indexval: DWORD) (offset:DWORD) (r: BaseReg AdSize4) (r1:IxReg AdSize4) sc :
  |-- basic (r ~= v ** r1 ~= indexval)
            (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ (Some(mkSIB _ r (Some(r1, sc)))) offset))) empOP
            (r ~= computeIxAdr (a:=AdSize4) v offset (scaleBy sc indexval) ** r1 ~= indexval).
Proof. Admitted. (*do_instrrule_triple. Qed.*)

Lemma LEA_rule (old v indexval offset: DWORD) (r r': GPReg32) (r1:NonSPReg32) sc :
  |-- basic (r ~= old ** r' ~= v ** r1 ~= indexval)
            (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ (Some(mkSIB _ r' (Some(r1, sc)))) offset))) empOP
            (r ~= addB (addB v offset) (scaleBy sc indexval) ** r' ~= v ** r1 ~= indexval).
Proof. Admitted. (*do_instrrule_triple. Qed.*)

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (offset : DWORD) (r : GPReg32) (r1 : NonSPReg32) sc,
                   instrrule (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ (Some(mkSIB _ r (Some(r1, sc)))) offset))) | 0
  := fun offset r r1 sc v indexval => @LEA_ruleSameBase32 v indexval offset r r1 sc.
Global Instance: forall (offset : DWORD) (r r' : GPReg32) (r1 : NonSPReg32) sc,
                   instrrule (instr.LEA _ r (RegMemM _ _ (mkMemSpec _ (Some(mkSIB _ r' (Some(r1, sc)))) offset))) | 1
  := fun offset r r' r1 sc old v indexval => @LEA_rule old v indexval offset r r' r1 sc.
