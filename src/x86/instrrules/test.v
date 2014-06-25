(** * TEST instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import bitsopsprops (* for [andBB] *).

Lemma TEST_self_rule (r:Reg) (v:DWORD) :
  |-- basic (r ~= v ** OSZCP?) (TEST r, r)
            (r ~= v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  change (stateIs r) with (@DWORDorBYTEregIs true r).
  do_instrrule (instrrule_triple_bazooka; rewrite andBB; instrrule_triple_bazooka).
Qed.
