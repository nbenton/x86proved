(** * LEA instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.x86.eval (* for [scaleBy] *).

Lemma LEA_ruleSameBase (v indexval offset: DWORD) (r: Reg) (r1:NonSPReg) sc :
  |-- basic (r ~= v ** r1 ~= indexval)
            (instr.LEA r (RegMemM _ (mkMemSpec (Some(r, Some(r1, sc))) offset))) empOP
            (r ~= addB (addB v offset) (scaleBy sc indexval) ** r1 ~= indexval).
Proof. do_instrrule_triple. Qed.

Lemma LEA_rule (old v indexval offset: DWORD) (r r': Reg) (r1:NonSPReg) sc :
  |-- basic (r ~= old ** r' ~= v ** r1 ~= indexval)
            (instr.LEA r (RegMemM _ (mkMemSpec (Some(r', Some(r1, sc))) offset))) empOP
            (r ~= addB (addB v offset) (scaleBy sc indexval) ** r' ~= v ** r1 ~= indexval).
Proof. do_instrrule_triple. Qed.
