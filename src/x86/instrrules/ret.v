(** * RET instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma RET_rule p' (sp:DWORD) (offset:WORD) (p q: DWORD) O :
  let sp':DWORD := addB (sp+#4) (zeroExtend 16 offset) in
  |-- (
         obs O @ (EIP ~= p' ** ESP ~= sp' ** sp :-> p') -->>
         obs O @ (EIP ~= p  ** ESP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RETOP offset).
Proof.
  apply: TRIPLE_safe => R.
  do_instrrule_triple.
Qed.

Lemma RET_loopy_rule p' (sp:DWORD) (offset:WORD) (p q: DWORD) O `{IsPointed_OPred O} :
  let sp':DWORD := addB (sp+#4) (zeroExtend 16 offset) in
  |-- (
      |> obs O @ (EIP ~= p' ** ESP ~= sp' ** sp :-> p') -->>
         obs O @ (EIP ~= p  ** ESP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RETOP offset).
Proof.
  apply: TRIPLE_safeLater => R.
  do_instrrule_triple.
Qed.

(** We make this rule an instance of the typeclass, after unfolding various things in its type. *)
Section handle_type_of_rule.
  Context (offset : WORD).
  Let rule := (fun p' sp => @RET_rule p' sp offset).
  Let loopy_rule := (fun p' sp => @RET_loopy_rule p' sp offset).
  Let T := Eval cbv beta iota zeta in (fun T (x : T) => T) _ rule.
  Let loopy_T := Eval cbv beta iota zeta in (fun T (x : T) => T) _ loopy_rule.
  Global Instance: instrrule (RETOP offset) := rule : T.
  Global Instance: instrrule_loopy (RETOP offset) := loopy_rule : loopy_T.
End handle_type_of_rule.
