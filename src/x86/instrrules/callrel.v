(** * CALL (rel) instruction *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred OPred septac spec obs triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

Lemma CALLrel_rule (p q: DWORD) (tgt: JmpTgt) (w sp:DWORD) O :
  |-- interpJmpTgt tgt q (fun P p' =>
      ( 
      |> obs O @ (EIP ~= p' ** P ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** P ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel tgt)).
Proof.
  rewrite /interpJmpTgt/interpMemSpecSrc.
  do_instrrule
    ((try specintros => *; autorewrite with push_at);
     apply TRIPLE_safe => ?;
     do !instrrule_triple_bazooka_step idtac).
Qed.

Section specapply_hint.
Local Hint Unfold interpJmpTgt : specapply.

Corollary CALLrel_R_rule (r:Reg) (p q: DWORD) :
  |-- Forall O, Forall w: DWORD, Forall sp:DWORD, Forall p', (
      |> obs O @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof.
  specintros => O w sp p'.
  specapply (CALLrel_rule p q (JmpTgtR r)). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.

Corollary CALLrel_I_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall O, Forall w: DWORD, Forall sp:DWORD, (
      |> obs O @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof.
  specintros => O w sp.
  specapply (CALLrel_rule p q (JmpTgtI rel)). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.
End specapply_hint.
