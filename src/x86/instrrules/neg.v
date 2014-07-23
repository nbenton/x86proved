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

(** We make this rule an instance of the typeclass, after unfolding various things in its type. *)
Section handle_type_of_rule.
  Section true.
    Context (r : Reg).
    Let rule := @NEG_R_rule true r.
    Let T := Eval cbv beta iota zeta delta [makeUOP DWORDorBYTEregIs InstrArg_of_DWORDorBYTEReg] in (fun T (x : T) => T) _ rule.
    Global Instance: instrrule (UOP true OP_NEG (RegMemR true r)) := rule : T.
  End true.
  Section false.
    Context (r : BYTEReg).
    Let rule := @NEG_R_rule false r.
    Let T := Eval cbv beta iota zeta delta [makeUOP DWORDorBYTEregIs InstrArg_of_DWORDorBYTEReg] in (fun T (x : T) => T) _ rule.
    Global Instance: instrrule (UOP false OP_NEG (RegMemR false r)) := rule : T.
  End false.
  (** TODO(t-jagro): This might be scary to those who aren't
                     comfortable with dependent types.  Maybe we
                     should drop it, or update [NEG_R_rule] to use
                     [UOP] rather than [NEG] (which goes through the
                     very silly [InstrArg_of_DWORDorBYTEReg]
                     coercion. *)
  Section generic1.
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
  End generic1.
  Section generic2.
    Context d (r : DWORDorBYTEReg d).
    Let rule := @NEG_R_rule d r.
    Let T := Eval cbv beta iota zeta delta [makeUOP] in (fun T (x : T) => T) _ rule.
    Global Instance: instrrule (NEG r) := rule : T.
  End generic2.
End handle_type_of_rule.
