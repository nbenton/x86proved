(** * NEG instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** Special case for negation *)
Lemma NEG_R_rule s (r:VReg s) (v:VWORD s) :
  let w := negB v in
  |-- basic
    (r ~= v ** OSZCP?) (NEG r) empOP
    (r ~= w ** OSZCP (msb v!=msb w) (msb w) (w == #0) (v != #0) (lsb w)).
Proof. destruct s; do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (r : VReg s), instrrule (NEG r) := @NEG_R_rule.
(** TODO(t-jagro): This might be scary to those who aren't comfortable
                   with dependent types.  Maybe we should drop it, or
                   update [NEG_R_rule] to use [UOP] rather than [NEG] *)
Section generic.
  Let rule s (r : VReg s) := @NEG_R_rule s r.
  Let T s (r : VReg s) := Eval cbv beta iota zeta delta [makeUOP] in (fun T (x : T) => T) _ (@rule s r).
  Global Instance: forall s r, instrrule (UOP s OP_NEG (RegMemR s r)) :=
    fun s r => match s as s return forall r, @T s r -> forall v : VWORD s,
                                                         |--basic
                                                            (r ~= v ** OF? ** SF? ** ZF? ** CF? ** PF?)
                                                            (UOP s OP_NEG (RegMemR s r)) empOP
                                                            (r ~= (negB v) **
                                                                              OSZCP (msb v != msb (negB v)) (msb (negB v))
                                                                              (negB v == #(0)) (v != #(0)) (lsb (negB v))) with
                 | OpSize1 => fun r x => x
                 | OpSize2 => fun r x => x
                 | OpSize4 => fun r x => x 
              end r (@rule s r).
End generic.
