(** * XOR instruction *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

Lemma XOR_RR_rule d (r1 r2:DWORDorBYTEReg d) v1 (v2:DWORDorBYTE d):
  |-- basic (DWORDorBYTEregIs r1 v1 ** DWORDorBYTEregIs r2 v2 ** OSZCP?) (XOR r1, r2)
            (DWORDorBYTEregIs r1 (xorB v1 v2) ** DWORDorBYTEregIs r2 v2 ** OSZCP false (msb (xorB v1 v2))
                            (xorB v1 v2 == #0) false (lsb (xorB v1 v2))).
Proof. destruct d; do_instrrule_triple. Qed.

Lemma XOR_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  xorB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (XOR r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. change (stateIs r1) with (@DWORDorBYTEregIs true r1). move => ?; subst. do_instrrule_triple. Qed.

(** We open a section in order to localize the hints *)
Section InstrRules.

Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : basicapply.
Hint Rewrite
  addB0 low_catB : basicapply.

Hint Unfold OSZCP stateIsAny : spred.

Corollary XOR_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (XOR r1, [r2 + offset]) (r1~=xorB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. basicapply (@XOR_RM_rule pd r1 r2 v1 v2 offset (xorB v1 v2) (refl_equal _)). Qed.
End InstrRules.
