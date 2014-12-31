(** * SHL and SHR instructions *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.bitsopsprops (* for [dropmsb_iter_shlB] *).

(** Lazy man's proof *)
Lemma SmallCount : forall count, count < 32 -> toNat (n:=8) (andB #x"1f" (fromNat count)) = count.
Proof. do 32 case => //.
Qed.

Lemma SmallCount64 : forall count, count < 64 -> toNat (n:=8) (andB #x"3f" (fromNat count)) = count.
Proof. do 64 case => //.
Qed.

Lemma SHL_RI_rule s (r:GPReg s) (v:VWORD s) (count:nat) o sf z c p:
  count < (if s is OpSize8 then n64 else n32) ->
  |-- basic (r~=v ** OSZCP o sf z c p) (SHL r, count) 
            (r~=iter count shlB v ** OSZCP?).
Proof.
  move => BOUND.
  (** We don't want to spin forever if something goes wrong, so we
      only allow [count] to be destructed 5 times.  We do it in the
      middle of the proof to reduce proof term size. *)
  destruct s;
  do 5?[do ![ progress instrrule_triple_bazooka using sbazooka
            | progress rewrite (SmallCount64 BOUND)
            | progress rewrite (SmallCount BOUND)
            | progress rewrite /stateIsAny ]
       | destruct count as [|count]; rewrite /(iter 0) ?dropmsb_iter_shlB ].
Qed.

Lemma SHR_RI_rule s (r:GPReg s) (v:VWORD s) (count:nat) o sf z c p:
  count < (if s is OpSize8 then n64 else n32) ->
  |-- basic (r~=v ** OSZCP o sf z c p) (SHR r, count)
            (r~=iter count shrB v ** OSZCP?).
Proof.
  move => BOUND.
  (** We don't want to spin forever if something goes wrong, so we
      only allow [count] to be destructed 5 times.  We do it in the
      middle of the proof to reduce proof term size. *)
  destruct s;
  do 5?[do ![ progress instrrule_triple_bazooka using sbazooka
            | progress rewrite (SmallCount BOUND)
            | progress rewrite (SmallCount64 BOUND)
            | progress rewrite /stateIsAny ]
       | destruct count as [|count]; rewrite /(iter 0) ?droplsb_iter_shrB ].
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (r : GPReg s) (count : nat), instrrule (SHL r, count) := fun s r count v => @SHL_RI_rule s r v count.
Global Instance: forall s (r : GPReg s) (count : nat), instrrule (SHR r, count) := fun s r count v => @SHR_RI_rule s r v count.
