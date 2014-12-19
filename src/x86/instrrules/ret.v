(** * RET instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma RET_rule p' (sp:DWORD) (offset:WORD) (p q: DWORD) :
  let sp':DWORD := addB (sp+#4) (zeroExtend 16 offset) in
  |-- (
         safe @ (EIP ~= p' ** ESP ~= sp' ** sp :-> p') -->>
         safe @ (EIP ~= p  ** ESP ~= sp  ** sp :-> p')
    ) c@ (p -- q :-> RETOP offset).
Proof.
  do_instrrule_triple.
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall offset : WORD, instrrule (RETOP offset) := fun offset p' sp => @RET_rule p' sp offset.
