(** * ADC instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** TODO(t-jagro): Generalize this to [VWORD] *)
Lemma ADC_rule s (ds:DstSrc s) v1 Of Sf Zf (Cf : bool) Pf
: |-- specAtDstSrc ds (fun D v2 =>
                         basic (D v1 ** OSZCP Of Sf Zf Cf Pf)
                               (BOP _ OP_ADC ds)
                               (let (carry, v) := eta_expand (adcB Cf v1 v2) in
                                D v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall d (ds : DstSrc d), instrrule (BOP d OP_ADC ds) := @ADC_rule.

Lemma ADC_RI_rule_helper (r1:GPReg32) v1 (v2:DWORD) o s z c p
: let: (carry, v) := eta_expand (adcB c v1 v2) in
  |-- (basic (r1~=v1 ** OSZCP o s z c p)
             (ADC r1, v2) 
             (r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                (v == #0) carry (lsb v))).
Proof. unfold BOPArgI4. basic apply *. Qed.

Lemma ADC_RI_rule (r1:GPReg32) v1 (v2:DWORD) carry v o s z c p
: adcB c v1 v2 = (carry, v) ->
  |-- (basic (r1~=v1 ** OSZCP o s z c p)
             (ADC r1, v2) 
             (r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                (v == #0) carry (lsb v))).
Proof.
  move => H. generalize (@ADC_RI_rule_helper r1 v1 v2 o s z c p).
  by rewrite H.
Qed.
