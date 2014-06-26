(** * RET instruction *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec OPred obs triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

Lemma RET_rule p' (sp:DWORD) (offset:WORD) (p q: DWORD) O :
  let sp':DWORD := addB (sp+#4) (zeroExtend 16 offset) in
  |-- (
      |> obs O @ (EIP ~= p' ** ESP ~= sp' ** sp :-> p') -->>
         obs O @ (EIP ~= p  ** ESP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RETOP offset).
Proof.
  apply TRIPLE_safe => R. 
  do_instrrule_triple.
Qed.
