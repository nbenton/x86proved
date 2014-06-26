(** * LEA instruction *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec OPred triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

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
