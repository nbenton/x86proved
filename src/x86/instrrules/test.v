(** * TEST instruction *)
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

Lemma TEST_self_rule (r:Reg) (v:DWORD) :
  |-- basic (r ~= v ** OSZCP?) (TEST r, r)
            (r ~= v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  change (stateIs r) with (@DWORDorBYTEregIs true r).
  do_instrrule (instrrule_triple_bazooka; rewrite andBB; instrrule_triple_bazooka).
Qed.
