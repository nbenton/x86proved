(** * RET instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma RET_rule p' (sp:ADDR) (offset:WORD) (p q: ADDR) :
  let sp':ADDR := addB (sp+#8) (zeroExtend _ offset) in
  |-- (
         safe @ (UIP ~= p' ** USP ~= sp' ** sp :-> p') -->>
         safe @ (UIP ~= p  ** USP ~= sp  ** sp :-> p')
    ) c@ (p -- q :-> RETOP offset).
Proof.
  do_instrrule_triple.
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall offset : WORD, instrrule (RETOP offset) := fun offset p' sp => @RET_rule p' sp offset.
