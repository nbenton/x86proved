Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.opred x86proved.septac x86proved.spectac x86proved.spec x86proved.obs x86proved.pointsto x86proved.cursor x86proved.x86.instr.
Require Import x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.instrsyntax x86proved.x86.macros x86proved.x86.instrrules.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.

Definition retreg := EBP.

(* Toy function calling convention *)
Definition toyfun f P O Q :=
  Forall iret, Forall O', 
               obs O' @ (EIP~=iret ** retreg? ** Q)
          -->> obs (catOP O O') @ (EIP~=f ** retreg~=iret ** P).

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

Lemma spec_at_toyfun f P O Q R:
  toyfun f P O Q @ R -|- toyfun f (P**R) O (Q**R).
Proof.
  rewrite /toyfun.
  autorewrite with push_at. cancel1 => iret. 
  autorewrite with push_at. cancel1 => O'. 
  autorewrite with push_at. rewrite !sepSPA. by cancel1.
Qed.
Hint Rewrite spec_at_toyfun : push_at.

Lemma toyfun_call (f:DWORD) P (O:OPred) Q:
  |> toyfun f P O Q |-- basic P (call_toyfun f) O Q @ retreg?.
Proof.
  autorewrite with push_at. rewrite /call_toyfun.
  apply basic_local => iret. rewrite /stateIsAny. specintros => old.  
  eapply (basic_seq _ _ _ _ empOP _ O). done. 
  eapply basic_basic. apply MOV_RI_rule. ssimpl. reflexivity. reflexivity. 

  rewrite /basic. specintros => i j O'. unfold_program. specintros => _ <- -> {j}.
  specapply JMP_I_rule. by ssimpl.

  rewrite <-spec_reads_frame. autorewrite with push_at.
  rewrite /toyfun. 
  autorewrite with push_later; last by apply _. apply lforallL with iret.
  autorewrite with push_later; last by apply _. apply lforallL with O'.
  rewrite /stateIsAny. autorewrite with push_later; last by apply _.
  rewrite <- spec_later_weaken.
  cancel2. cancel1. by ssimpl.
Qed.   

Lemma toyfun_mkbody (f f': DWORD) P p O Q:
  (Forall iret, basic P p O Q @ (retreg ~= iret)) |--
    toyfun f P O Q <@ (f--f' :-> mkbody_toyfun p).
Proof.
  rewrite /toyfun. specintro => iret. rewrite /mkbody_toyfun.
  unfold_program. specintro => i1.
  apply lforallL with iret. autorewrite with push_at.
  specintros => O'. 
  eapply safe_safe_ro; first reflexivity. reflexivity.
  - apply lforallL with f. apply lforallL with i1. apply lforallL with O'. reflexivity.
  - split; sbazooka.
  specapply JMP_R_rule. by ssimpl.
  rewrite <-spec_reads_frame. apply: limplAdj. apply: landL2.
  rewrite <-spec_later_weaken. rewrite /stateIsAny. autorewrite with push_at.
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

Example toyfun_example_callee_correct (f f': DWORD):
  |-- (Forall a, toyfun f (EAX ~= a) empOP (EAX ~= a +# 2))
        @ OSZCP? <@ (f--f' :-> toyfun_example_callee).
Proof.
  specintro => a. autorewrite with push_at.
  etransitivity; [|apply toyfun_mkbody]. specintro => iret.
  autorewrite with push_at. rewrite /stateIsAny.
  specintros => o s z c p.
  try_basicapply INC_R_rule; rewrite /OSZCP; sbazooka.
  try_basicapply INC_R_rule; rewrite /OSZCP; sbazooka.
  rewrite addIsIterInc /OSZCP /iter; sbazooka.
Qed.

(* The toyfun spec assumed for f here is actually stronger than what lemma
   toyfun_example_callee_correct guarantees: we ask for a function that does
   not have OSZCP? in its footprint. But thanks to the higher-order frame
   rule, it will still be possible to compose the caller and the callee. *)
(** TODO(t-jagro): Find a better way of doing this, or a better place for this. *)
Local Opaque spec_at.
Example toyfun_example_caller_correct a (f:DWORD):
  Forall a', toyfun f (EAX ~= a') empOP (EAX ~= a' +# 2)
  |-- basic (EAX ~= a) (toyfun_example_caller f) empOP (EAX ~= a +# 4) @ retreg?.
Proof.
  rewrite /toyfun_example_caller. rewrite /RegOrFlag_target.
  autorewrite with push_at.
  eapply basic_seq; first done.
  - apply lforallL with a.
    eapply basic_basic_context.
    - have H := toyfun_call. setoid_rewrite spec_at_basic in H. apply H.
    - by apply spec_later_weaken.
    - by sbazooka.
    done.
  reflexivity. 
  apply lforallL with (a +# 2).
  eapply basic_basic_context.
  - have H := toyfun_call. setoid_rewrite spec_at_basic in H. apply H.
  - by apply spec_later_weaken.
  - by ssimpl.
  reflexivity. rewrite -addB_addn. sbazooka. reflexivity.
Qed.

Example toyfun_example_correct entry (i j: DWORD) a O:
  |-- (
      obs O @ (EIP ~= j ** EAX ~= a +# 4) -->>
      obs O @ (EIP ~= entry ** EAX ~= a)
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
  eapply safe_safe_ro; first reflexivity. reflexivity. 
  - eapply lforallL. eapply lforallL. apply lforallL with O. rewrite ->empOPL. reflexivity.
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
Example toyfun_apply_correct (f f' g: DWORD) P O Q:
  |-- (
      toyfun g (P ** EBX?) O Q -->> toyfun f (P ** EBX ~= g) O Q
    ) <@ (f--f' :-> toyfun_apply).
Proof.
  rewrite /toyfun_apply. rewrite {2}/toyfun.
  specintro => iret. specintros => O'. rewrite limpland.
  specapply JMP_R_rule. by ssimpl.
  autorewrite with push_at.
  rewrite <-spec_reads_frame. rewrite -limpland. apply limplValid.
  rewrite /toyfun. eapply lforallL. eapply lforallL. rewrite <-spec_later_weaken.
  rewrite /stateIsAny. cancel2; cancel1; by sbazooka. 
Qed.
