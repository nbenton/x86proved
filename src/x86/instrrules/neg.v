(** * NEG instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** Special case for negation *)
Lemma NEG_R_rule d (r:DWORDorBYTEReg d) (v:DWORDorBYTE d) :
  let w := negB v in
  |-- basic
    (DWORDorBYTEregIs r v ** OSZCP?) (NEG r) empOP
    (DWORDorBYTEregIs r w ** OSZCP (msb v!=msb w) (msb w) (w == #0) (v != #0) (lsb w)).
Proof. destruct d; do_instrrule_triple. Qed.
