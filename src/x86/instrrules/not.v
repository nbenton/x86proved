(** * NOT instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma NOT_rule d (src:RegMem d) v:
  |-- specAtRegMemDst src (fun V => basic (V v) (UOP d OP_NOT src) empOP (V (invB v))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, after unfolding various things in its type. *)
Section handle_type_of_rule.
  Context d (src : RegMem d).
  Let rule := @NOT_rule d src.
  Let T := Eval cbv beta iota zeta delta [specAtRegMemDst] in (fun T (x : T) => T) _ rule.
  Global Instance: instrrule (UOP d OP_NOT src) := rule : T.
End handle_type_of_rule.

Ltac basicNOT :=
  rewrite /makeUOP;
  let R := lazymatch goal with
             | |- |-- basic ?p (@UOP ?d OP_NOT ?a) ?O ?q => constr:(@NOT_rule d a)
           end in
  instrrules_basicapply R.


(** Special case for not *)
Lemma NOT_R_rule (r:Reg) (v:DWORD):
  |-- basic (r~=v) (NOT r) empOP (r~=invB v).
Proof. basicNOT. Qed.

Corollary NOT_M_rule (r:Reg) (offset:nat) (v pbase:DWORD):
  |-- basic (r~=pbase ** pbase +# offset :-> v) (NOT [r + offset]) empOP
            (r~=pbase ** pbase +# offset :-> invB v).
Proof. basicNOT. Qed.
