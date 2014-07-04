(** * RET instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma RET_rule p' (sp:DWORD) (offset:WORD) (p q: DWORD) O :
  let sp':DWORD := addB (sp+#4) (zeroExtend 16 offset) in
  |-- (
      |> obs O @ (EIP ~= p' ** ESP ~= sp' ** sp :-> p') -->>
         obs O @ (EIP ~= p  ** ESP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RETOP offset).
Proof.
  apply TRIPLE_safeLater => R. 
  do_instrrule_triple.
Qed.
