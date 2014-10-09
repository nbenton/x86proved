(** * NOT instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma NOT_rule d (src:RegMem d) v:
  |-- specAtRegMemDst src (fun V => basic (V v) (UOP d OP_NOT src) empOP (V (invB v))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall d (src : RegMem d), instrrule (UOP d OP_NOT src) := @NOT_rule.


(** Special case for not *)
Lemma NOT_R_rule (r:GPReg32) (v:DWORD):
  |-- basic (r~=v) (NOT r) empOP (r~=invB v).
Proof. basic apply *. Qed.

(*
(* BUG: default for NOT syntax on pointers appears to be dword size. *)
Corollary NOT_M_rule (r:GPReg64) (offset:nat) (pbase:ADDR) (v:QWORD):
  |-- basic (r~=pbase ** eval.computeAddr (a:=AdSize8) pbase offset :-> v) (NOT [r + offset]) empOP
            (r~=pbase ** eval.computeAddr (a:=AdSize8) pbase offset :-> invB v).
Proof. (*attempt basic apply *. *)
 attempt basic apply (NOT_rule (d:=OpSize8)).  *. setoid_rewrite empSPR. Set Printing All. Show. 
(* OK, we seem to have a default points-to of size 4 here. Why? *)
reflexivity. ssimpl. Set Printing Coercions. sbazooka.  Show. ssimpl. Qed.
*)