(** * INC and DEC instructions *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic increment/decrement rule *)
Lemma INCDEC_rule d (dir: bool) (src:RegMem d) oldv o s z c pf:
  |-- specAtRegMemDst src (fun V =>
      basic (V oldv ** OSZCP o s z c pf) (if dir then UOP d OP_INC src else UOP d OP_DEC src)
      empOP
      (let w := if dir then incB oldv else decB oldv in
      V w ** OSZCP (msb oldv!=msb w) (msb w) (w == #0) c (lsb w))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, after unfolding various things in its type. *)
Section handle_type_of_rule.
  Context d (src : RegMem d).
  Let rule dir := @INCDEC_rule d dir src.
  Let TI := Eval cbv beta iota zeta delta [specAtRegMemDst] in (fun T (x : T) => T) _ (rule true).
  Let TD := Eval cbv beta iota zeta delta [specAtRegMemDst] in (fun T (x : T) => T) _ (rule false).
  Global Instance: instrrule (UOP d OP_INC src) := rule true : TI.
  Global Instance: instrrule (UOP d OP_DEC src) := rule false : TD.
End handle_type_of_rule.

Definition INC_rule := Eval hnf in @INCDEC_rule true true.
Definition DEC_rule := Eval hnf in @INCDEC_rule true false.

Ltac basicINCDEC :=
  rewrite /makeUOP;
  let R := lazymatch goal with
             | |- |-- basic ?p (@UOP ?d OP_INC ?a) ?O ?q => constr:(@INCDEC_rule d true a)
             | |- |-- basic ?p (@UOP ?d OP_DEC ?a) ?O ?q => constr:(@INCDEC_rule d false a)
           end in
  instrrules_basicapply R.

(** Special case for increment register *)
Corollary INC_R_rule (r:Reg) (v:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (INC r) empOP
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Corollary INC_M_rule (r:Reg) (offset:nat) (v pbase:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** OSZCP o s z c pf) (INC [r + offset]) empOP
            (r ~= pbase ** pbase +# offset :-> w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Lemma INC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (INC r) empOP (r~=incB v) @ OSZCP?.
Proof.
  autorewrite with push_at. rewrite /stateIsAny. specintros => *.
  basicINCDEC.
Qed.

(* Special case for decrement *)
Lemma DEC_R_rule (r:Reg) (v:DWORD) o s z c pf :
  let w := decB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (DEC r) empOP
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Lemma DEC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (DEC r) empOP (r~=decB v) @ OSZCP?.
Proof.
  autorewrite with push_at. rewrite /stateIsAny. specintros => *.
  basicINCDEC.
Qed.
