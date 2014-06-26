(** * NEG instruction *)
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

(** Special case for negation *)
Lemma NEG_R_rule d (r:DWORDorBYTEReg d) (v:DWORDorBYTE d) :
  let w := negB v in
  |-- basic
    (DWORDorBYTEregIs r v ** OSZCP?) (NEG r) empOP
    (DWORDorBYTEregIs r w ** OSZCP (msb v!=msb w) (msb w) (w == #0) (v != #0) (lsb w)).
Proof. destruct d; do_instrrule_triple. Qed.
