Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spectac x86proved.spec x86proved.safe x86proved.pointsto x86proved.cursor x86proved.x86.instr.
Require Import x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.instrsyntax x86proved.x86.macros x86proved.x86.instrrules.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import x86proved.common_tactics x86proved.basicspectac x86proved.chargetac.

Definition retreg := EBP.

(* Toy function calling convention *)
Definition toyfun f P Q :=
  Forall iret,
  safe @ (EIP~=iret ** retreg? ** Q)
      -->> safe @ (EIP~=f ** retreg~=iret ** P).

(* Use this macro for calling f *)
Definition call_toyfun f :=
  (LOCAL iret;
   MOV retreg, iret;; JMP f;;
   iret:;)
    %asm.

(* Use this macro to make a function that returns in the end *)
Definition mkbody_toyfun (p: program) :=
  p;; JMP retreg.

(* It's useful to define local functions *)
Notation "'let_toyfun' f  ':=' p 'in' q" :=
  (LOCAL skip; JMP skip;; LOCAL f; f:;; mkbody_toyfun p;; skip:;; q)%asm
                                                                    (at level 45, f ident, right associativity).

Lemma spec_at_toyfun f P Q R:
  toyfun f P Q @ R -|- toyfun f (P**R) (Q**R).
Proof.
  rewrite /toyfun.
  autorewrite with push_at. cancel1 => iret.
  autorewrite with push_at. rewrite -> !sepSPA. by cancel1.
Qed.
Hint Rewrite @spec_at_toyfun : push_at.

Lemma toyfun_call (f:DWORD) P Q:
  toyfun f P Q |-- basic P (call_toyfun f) Q @ retreg?.
Proof.
  autorewrite with push_at. rewrite /call_toyfun.
  basic apply * => iret.
  rewrite /stateIsAny. specintros => *.
  basic apply *.

  rewrite /basic. specintros => i j. unfold_program. specintros => *; do !subst.
  specapply *; first by ssimpl.

  rewrite <-spec_reads_frame. autorewrite with push_at.
  rewrite /toyfun.
  apply lforallL with iret.
  rewrite /stateIsAny.
  cancel2. cancel1. by ssimpl.
Qed.

Global Opaque call_toyfun.
Global Instance: forall f : DWORD, instrrule (call_toyfun f) := @toyfun_call.

Lemma toyfun_mkbody (f f': DWORD) P p Q:
  (Forall iret, basic P p Q @ (retreg ~= iret))
    |-- toyfun f P Q <@ (f--f' :-> mkbody_toyfun p).
Proof.
  rewrite /toyfun. specintro => iret. rewrite /mkbody_toyfun.
  unfold_program. specintro => i1.
  apply lforallL with iret. autorewrite with push_at.
  eapply safe_safe_ro; first reflexivity. 
  - apply lforallL with f. apply lforallL with i1. reflexivity.
  - split; sbazooka.
    specapply *; first by ssimpl.
    rewrite <-spec_reads_frame. apply: limplAdj. apply: landL2.
    rewrite /stateIsAny. autorewrite with push_at.
    cancel1. by sbazooka.
Qed.


(*
   Example that shows a caller and a callee independently verified and then
   composed.
 *)

Definition toyfun_example_callee : program :=
  mkbody_toyfun (
      INC EAX;;
          INC EAX
    )%asm.

Definition toyfun_example_caller f : program :=
  call_toyfun f;;
  call_toyfun f.

Definition toyfun_example (entry: DWORD) : program :=
  LOCAL f;
  f:;;
   toyfun_example_callee;;
   entry:;;
   toyfun_example_caller f.

Example toyfun_example_callee_correct_helper (f f': DWORD):
  |-- (Forall a, toyfun f (EAX ~= a) (EAX ~= a +# 2))
      @ OSZCP? <@ (f--f' :-> toyfun_example_callee).
Proof.
  specintro => a. autorewrite with push_at.
  etransitivity; [|apply toyfun_mkbody]. specintro => iret.
  autorewrite with push_at. rewrite /stateIsAny.
  specintros => o s z c p.
  do ?attempt basic apply *;
  repeat match goal with
           | _ => progress intros
           | _ => evar_safe_syntax_unify_reflexivity
         end.
  by rewrite addIsIterInc /iter.
Qed.

Definition toyfun_example_callee_correct (f f': DWORD):
  |-- (Forall a, toyfun f (EAX ~= a) (EAX ~= a +# 2))
      @ OSZCP? <@ (f--f' :-> toyfun_example_callee)
  := @toyfun_example_callee_correct_helper f f'.

(*
Definition loopy_toyfun_example_callee_correct (f f': DWORD):
  |-- (Forall a, loopy_toyfun f (EAX ~= a) empOP (EAX ~= a +# 2))
      @ OSZCP? <@ (f--f' :-> toyfun_example_callee)
  := @toyfun_example_callee_correct_helper PointedOPred OPred_pred (fun O1 O2 => mkPointedOPred (catOP O1 O2) _) (mkPointedOPred empOP _)
                                           f f' (fun _ _ => reflexivity _) (reflexivity _).

*)

(* The toyfun spec assumed for f here is actually stronger than what lemma
   toyfun_example_callee_correct guarantees: we ask for a function that does
   not have OSZCP? in its footprint. But thanks to the higher-order frame
   rule, it will still be possible to compose the caller and the callee. *)
(** TODO(t-jagro): Find a better way of doing this, or a better place for this [Opaque]. *)
Local Opaque spec_at.
Example toyfun_example_caller_correct a (f:DWORD):
  Forall a', toyfun f (EAX ~= a') (EAX ~= a' +# 2)
                    |-- basic (EAX ~= a) (toyfun_example_caller f) (EAX ~= a +# 4) @ retreg?.
Proof.
  rewrite /toyfun_example_caller. rewrite /RegOrFlag_target.
  autorewrite with push_at.
  eapply basic_seq. 
  (** FIXME: make [basic apply *] not take forever *)
  { apply lforallL with a.
    simple basic apply *; try evar_safe_syntax_unify_reflexivity; ssimpl. }
  { apply lforallL with (a +# 2).
    simple basic apply *; try evar_safe_syntax_unify_reflexivity; ssimpl.
    ssimpl.
    rewrite -addB_addn. reflexivity. }
Qed.

Example toyfun_example_correct entry (i j: DWORD) a:
  |-- (
      safe @ (EIP ~= j ** EAX ~= a +# 4) -->>
          safe @ (EIP ~= entry ** EAX ~= a)
    ) @ (retreg? ** OSZCP?) <@ (i--j :-> toyfun_example entry).
Proof.
  rewrite /toyfun_example. unfold_program.
  specintros => f _ <- -> {i} i1 _ <- ->. rewrite !empSPL.
  rewrite [X in _ <@ X]sepSPC. rewrite <-spec_reads_merge.
  rewrite ->toyfun_example_callee_correct.
  (* The following rewrite underneath a @ is essentially a second-order frame
     rule application. *)
  rewrite ->toyfun_example_caller_correct.
  cancel2; last reflexivity. autorewrite with push_at.
  eapply safe_safe_ro; first reflexivity. 
  - eapply lforallL. eapply lforallL. reflexivity.
  - split; sbazooka.
    rewrite <-spec_reads_frame. apply: limplAdj. apply: landL2.
    rewrite spec_at_emp. cancel1. sbazooka.
Qed.

(*
   Higher-order function example.
 *)

(* This simple definition is the implementation of a higher-order function. It
   takes a pointer to another function in EBX and calls that. *)
Definition toyfun_apply :=
  JMP EBX.

Lemma limpland (S1 S2 S3: spec) :
  S1 -->> S2 -->> S3 -|- S1 //\\ S2 -->> S3.
Proof.
  split.
  - apply: limplAdj.
    apply: limplL; first exact: landL1.
    apply: limplL; first exact: landL2. exact: landL1.
  - apply: limplAdj.  apply: limplAdj. rewrite landA.
    exact: landAdj.
Qed.

(* It is possible but does not seem necessary to put a |> in front of the -->>.
   There will be a function call somewhere to provide the |> unless we're just
   making the apply function call itself in a tight loop. *)
Example toyfun_apply_correct (f f' g: DWORD) P Q:
  |-- (
      toyfun g (P ** EBX?) Q -->> toyfun f (P ** EBX ~= g) Q
    ) <@ (f--f' :-> toyfun_apply).
Proof.
  rewrite /toyfun_apply. rewrite {2}/toyfun.
  specintro => iret. rewrite limpland.
  specapply *; first by ssimpl.
  autorewrite with push_at.
  rewrite <-spec_reads_frame. rewrite -limpland. apply limplValid.
  rewrite /toyfun. eapply lforallL. 
  rewrite /stateIsAny. cancel2; cancel1; by sbazooka.
Qed.
