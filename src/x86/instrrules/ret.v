(** * RET instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma RET_rule p' (sp:ADDR) (offset:WORD) (p q: ADDR) O :
  let sp' := addB (sp+#8) (zeroExtend _ offset) in
  |-- (
         obs O @ (UIP ~= p' ** USP ~= sp' ** sp :-> p') -->>
         obs O @ (UIP ~= p  ** USP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RETOP offset).
Proof.
  apply: TRIPLE_safe => R.
  do_instrrule_triple.
Qed.

Lemma RET_loopy_rule p' (sp:ADDR) (offset:WORD) (p q: ADDR) O `{IsPointed_OPred O} :
  let sp' := addB (sp+#8) (zeroExtend _ offset) in
  |-- (
      |> obs O @ (UIP ~= p' ** USP ~= sp' ** sp :-> p') -->>
         obs O @ (UIP ~= p  ** USP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RETOP offset).
Proof.
  apply: TRIPLE_safeLater => R.
  do_instrrule_triple.
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall offset : WORD, instrrule (RETOP offset) := fun offset p' sp => @RET_rule p' sp offset.
Global Instance: forall offset : WORD, loopy_instrrule (RETOP offset) := fun offset p' sp => @RET_loopy_rule p' sp offset.
