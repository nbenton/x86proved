(** * ADC instruction *)
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

Lemma ADC_RI_rule (r1:Reg) v1 (v2:DWORD) carry v o s z c p:
  adcB c v1 v2 = (carry,v) ->
  |-- basic (r1~=v1 ** OSZCP o s z c p) (ADC r1, v2)
            (r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof.
  move => H.
  change_stateIs_with_DWORDorBYTEregIs.
  do_instrrule (instrrule_triple_bazooka; try rewrite H; simpl fst; simpl snd; instrrule_triple_bazooka).
Qed.
