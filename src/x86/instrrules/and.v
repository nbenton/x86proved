(** * AND instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic AND *)
Lemma AND_rule sz (ds:DstSrc sz) (v1: VWORD sz) :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP _ OP_AND ds) 
             (let v := andB v1 v2 in
              D v ** OSZCP false (msb v) (v == #0) false (lsb v))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall sz (ds : DstSrc sz), instrrule (BOP sz OP_AND ds) := @AND_rule.

(** ** AND r1, r2 *)
Corollary AND_RR_rule (r1 r2:Reg) v1 (v2:DWORD) :
  |-- basic (r1~=v1 ** r2 ~= v2 ** OSZCP?)
            (AND r1, r2) 
            (let v := andB v1 v2 in r1~=v ** r2 ~= v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. basic apply *. Qed.

(** ** AND r1, [r2 + offset] *)
Corollary AND_RM_rule (pbase:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) :
  |-- basic (r1~=v1 ** OSZCP?)
            (AND r1, [r2 + offset]) 
            (let v:= andB v1 v2 in r1~=v ** OSZCP false (msb v) (v == #0) false (lsb v))
      @ (r2 ~= pbase ** pbase +# offset :-> v2).
Proof. autorewrite with push_at. basic apply *. Qed.

Corollary AND_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (AND r1, [r2 + offset]) (r1~=andB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. basic apply *. Qed.

(** ** AND r, v *)
Lemma AND_RI_rule (r:Reg) v1 (v2:DWORD) :
  |-- basic (r~=v1 ** OSZCP?)
            (AND r, v2) 
            (let v:= andB v1 v2 in r~=v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. basic apply *. Qed.
