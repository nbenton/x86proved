(** * OUT instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** Special case for negation *)
Lemma OUT_R_rule c d :
  |-- basic
      (BYTEregIs AL d) (OUT false c) (outOP c d) (BYTEregIs AL d).
Proof. Admitted.
