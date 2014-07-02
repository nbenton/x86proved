(** * OUT instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** Special case for negation *)
Lemma OUT_R_rule (c: BYTE) d :
  |-- basic
      (BYTEregIs AL d) (OUT c, AL) (outOP (zeroExtend 8 c) d) (BYTEregIs AL d).
Proof. Admitted.
