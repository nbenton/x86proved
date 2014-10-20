(** * LEA instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.x86.eval (* for [scaleBy] *).

Lemma LEA_ruleSameBase (v indexval offset: DWORD) (r: Reg) (r1:NonSPReg) sc :
  |-- basic (r ~= v ** r1 ~= indexval)
            (instr.LEA r (RegMemM _ (mkMemSpec (Some(r, Some(r1, sc))) offset))) 
            (r ~= addB (addB v offset) (scaleBy sc indexval) ** r1 ~= indexval).
Proof. do_instrrule_triple. Qed.

Lemma LEA_rule (old v indexval offset: DWORD) (r r': Reg) (r1:NonSPReg) sc :
  |-- basic (r ~= old ** r' ~= v ** r1 ~= indexval)
            (instr.LEA r (RegMemM _ (mkMemSpec (Some(r', Some(r1, sc))) offset))) 
            (r ~= addB (addB v offset) (scaleBy sc indexval) ** r' ~= v ** r1 ~= indexval).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (offset : DWORD) (r : Reg) (r1 : NonSPReg) sc,
                   instrrule (instr.LEA r (RegMemM _ (mkMemSpec (Some(r, Some(r1, sc))) offset))) | 0
  := fun offset r r1 sc v indexval => @LEA_ruleSameBase v indexval offset r r1 sc.
Global Instance: forall (offset : DWORD) (r r' : Reg) (r1 : NonSPReg) sc,
                   instrrule (instr.LEA r (RegMemM _ (mkMemSpec (Some(r', Some(r1, sc))) offset))) | 1
  := fun offset r r' r1 sc old v indexval => @LEA_rule old v indexval offset r r' r1 sc.
