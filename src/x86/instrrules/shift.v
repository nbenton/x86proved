(** * SHL and SHR instructions *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec OPred triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

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
