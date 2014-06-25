(** * RET instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import safe (* for [safe] *).

Lemma RET_rule p' (sp:DWORD) (offset:WORD) (p q: DWORD) :
  let sp':DWORD := addB (sp+#4) (zeroExtend 16 offset) in
  |-- (
      |> safe @ (EIP ~= p' ** ESP ~= sp' ** sp :-> p') -->>
         safe @ (EIP ~= p  ** ESP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RETOP offset).
Proof.
  apply TRIPLE_safe => R.
  do_instrrule_triple.
Qed.
