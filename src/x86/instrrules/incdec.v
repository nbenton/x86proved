(** * INC and DEC instructions *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic increment/decrement rule *)
Lemma INCDEC_rule sz (dir: bool) (src:RegMem sz) oldv o s z c pf:
  |-- specAtRegMemDst src (fun V =>
      basic (V oldv ** OSZCP o s z c pf) (if dir then UOP _ OP_INC src else UOP _ OP_DEC src)
      empOP
      (let w := if dir then incB oldv else decB oldv in
      V w ** OSZCP (msb oldv!=msb w) (msb w) (w == #0) c (lsb w))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall d (src : RegMem d), instrrule (UOP d OP_INC src) := fun d => @INCDEC_rule d true.
Global Instance: forall d (src : RegMem d), instrrule (UOP d OP_DEC src) := fun d => @INCDEC_rule d false.

Definition INC_rule := Eval hnf in @INCDEC_rule OpSize4 true.
Definition DEC_rule := Eval hnf in @INCDEC_rule OpSize4 false.

(** Special case for increment register *)
Corollary INC_R_rule (r:GPReg32) (v:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (INC r) empOP
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basic apply *. Qed.

Corollary INC_M_rule (r:GPReg32) (offset:nat) (v pbase:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r ~= pbase ** (eval.computeAddr (a:=AdSize4) pbase offset) :-> v ** OSZCP o s z c pf) (INC [r + offset]) empOP
            (r ~= pbase ** (eval.computeAddr (a:=AdSize4) pbase offset) :-> w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basic apply *. Qed.

Lemma INC_R_ruleNoFlags (r:GPReg32) (v:DWORD):
  |-- basic (r~=v) (INC r) empOP (r~=incB v) @ OSZCP?.
Proof.
  autorewrite with push_at. rewrite /stateIsAny. specintros => *.
  basic apply *.
Qed.

(* Special case for decrement *)
Lemma DEC_R_rule (r:GPReg32) (v:DWORD) o s z c pf :
  let w := decB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (DEC r) empOP
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basic apply *. Qed.

Lemma DEC_R_ruleNoFlags (r:GPReg32) (v:DWORD):
  |-- basic (r~=v) (DEC r) empOP (r~=decB v) @ OSZCP?.
Proof.
  autorewrite with push_at. rewrite /stateIsAny. specintros => *.
  basic apply *.
Qed.
