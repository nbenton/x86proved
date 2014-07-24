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

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall d (r : DWORDorBYTEReg d), instrrule (NEG r) := @NEG_R_rule.
(** TODO(t-jagro): This might be scary to those who aren't comfortable
                   with dependent types.  Maybe we should drop it, or
                   update [NEG_R_rule] to use [UOP] rather than [NEG]
                   (which goes through the very silly
                   [InstrArg_of_DWORDorBYTEReg] coercion. *)
Section generic.
  Let rule d (r : DWORDorBYTEReg d) := @NEG_R_rule d r.
  Let T d (r : DWORDorBYTEReg d) := Eval cbv beta iota zeta delta [makeUOP InstrArg_of_DWORDorBYTEReg] in (fun T (x : T) => T) _ (@rule d r).
  Global Instance: forall d r, instrrule (UOP d OP_NEG (RegMemR d r)) :=
    fun d r => match d as d return forall r, @T d r -> forall v : DWORDorBYTE d,
                                                         |--basic
                                                            (DWORDorBYTEregIs (d:=d) r v ** OF? ** SF? ** ZF? ** CF? ** PF?)
                                                            (UOP d OP_NEG (RegMemR d r)) empOP
                                                            (DWORDorBYTEregIs (d:=d) r (negB v) **
                                                                              OSZCP (msb v != msb (negB v)) (msb (negB v))
                                                                              (negB v == #(0)) (v != #(0)) (lsb (negB v))) with
                 | true => fun r x => x
                 | false => fun r x => x
               end r (@rule d r).
End generic.
