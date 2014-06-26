(** * SHL and SHR instructions *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import bitsopsprops (* for [dropmsb_iter_shlB] *).

(** Lazy man's proof *)
Lemma SmallCount : forall count, count < 32 -> toNat (n:=8) (andB #x"1f" (fromNat count)) = count.
Proof. do 32 case => //.
Qed.

Lemma SHL_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 ->
  |-- basic (r~=v ** OSZCP?) (SHL r, count) empOP
            (r~=iter count shlB v ** OSZCP?).
Proof.
  change (stateIs r) with (@DWORDorBYTEregIs true r).
  move => BOUND.
  (** We don't want to spin forever if something goes wrong, so we
      only allow [count] to be destructed 5 times.  We do it in the
      middle of the proof to reduce proof term size. *)
  do 5?[do ![ progress instrrule_triple_bazooka using sbazooka
            | progress rewrite (SmallCount BOUND)
            | progress rewrite /stateIsAny ]
       | destruct count as [|count]; rewrite /(iter 0) ?dropmsb_iter_shlB ].
Qed.

Lemma SHR_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 ->
  |-- basic (r~=v ** OSZCP?) (SHR r, count) empOP
            (r~=iter count shrB v ** OSZCP?).
Proof.
  change (stateIs r) with (@DWORDorBYTEregIs true r).
  move => BOUND.
  (** We don't want to spin forever if something goes wrong, so we
      only allow [count] to be destructed 5 times.  We do it in the
      middle of the proof to reduce proof term size. *)
  do 5?[do ![ progress instrrule_triple_bazooka using sbazooka
            | progress rewrite (SmallCount BOUND)
            | progress rewrite /stateIsAny ]
       | destruct count as [|count]; rewrite /(iter 0) ?droplsb_iter_shrB ].
Qed.
