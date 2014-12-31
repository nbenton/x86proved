Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.safe x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.macros.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor.
Require Import x86proved.spectac x86proved.basicspectac.
Require Import x86proved.common_tactics x86proved.chargetac x86proved.common_definitions x86proved.latertac.
Require Import Coq.Setoids.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Generalizable All Variables.

Local Open Scope instr_scope.

(* Example: It is safe to sit forever in a tight loop. *)
Example safe_loop (p q: ADDR) :
  |-- safe @ (UIP ~= p) c@ (p -- q :-> JMP p).
Proof.
  apply: spec_lob.
  superspecapply *. autorewrite with push_later. 
  finish_logic_with sbazooka. 
Qed.

(* Example: It is safe to sit forever in a tight loop. *)
Example safe_loopAlt (p r: ADDR) :
  |-- safe @ (UIP ~= p) c@ (p -- r :-> (JMP p;; NOP)).
Proof.
  apply: spec_lob.
  unfold_program. unfold_program. 
  specintros => q. superspecapply *. autorewrite with push_later.
  finish_logic_with sbazooka. 
Qed.


(* Example: It is safe to sit in a less tight loop forever. *)
Example safe_loop_while eax :
  |-- basic (EAX ~= eax ** OSZCP?) (while (TEST EAX, EAX) CC_O false prog_skip) lfalse.
Proof.
  basic apply (while_rule_ro (I := fun b => b == false /\\ EAX? ** SF? ** ZF? ** CF? ** PF?)) => //;
    rewrite /stateIsAny; specintros => *.
  do !basic apply *.
  basic apply TEST_self_rule.
Qed.

(* We can package up jumpy code in a triple by using labels. *)
Example basic_loop:
  |-- basic empSP (LOCAL l; l:;; JMP l) lfalse.
Proof.
  apply basic_local => l. 
  rewrite /basic. specintros => i j.
  unfold_program. specintros => _ <- <-. rewrite empSPL empSPR.
  
  rewrite spec_at_impl. apply limplValid. by rewrite <- safe_loop. 
Qed.

Example basic_loopAlt:
  |-- basic empSP (LOCAL l; l:;; (JMP l;; NOP)) lfalse.
Proof.
  apply basic_local => l. 
  rewrite /basic. specintros => i j.
  unfold_program. specintros => _ <- <- i'.  
  autorewrite with push_at.
  apply: limplAdj. apply: landL1. rewrite empSPL empSPR.
  etransitivity; [apply safe_loopAlt|]. autorewrite with push_at. cancel1. ssimpl.
  rewrite programMemIsSeq. sbazooka. rewrite programMemIsInstr. by ssimpl.
Qed.

(* Show off the sequencing rule for [basic]. *)
Example basic_inc3 (x:DWORD):
  |-- basic (EAX ~= x)
            (INC EAX;; INC EAX;; INC EAX) 
            (EAX ~= x +# 3) @ OSZCP?.
Proof.
  autorewrite with push_at. rewrite /stateIsAny.
  specintros => o s z c p.
  do !basic apply *.   
  rewrite addIsIterInc/iter. by ssimpl.
Qed.

Example incdec_while c a:
  |-- basic
    (ECX ~= c ** EAX ~= a)
    (
      while (TEST ECX, ECX) CC_Z false (
        DEC ECX;;
        INC EAX
      )
    ) 
    (ECX ~= #0 ** EAX ~= addB c a)
    @ OSZCP?.
Proof.
  autorewrite with push_at.
  instrrule remember (while_rule_ro (I := fun b => Exists c', Exists a',
    (c' == #0) = b /\\ addB c' a' = addB c a /\\
    ECX ~= c' ** EAX ~= a' **
    OF? ** SF? ** CF? ** PF?)).
  do ![ rewrite /stateIsAny; specintros => * | basic apply * ].
  { repeat match goal with
             | [ H : (_ == _) = true |- _ ] => move/eqP in H
             | _ => progress subst
             | _ => progress simpl in *
             | _ => progress ssimpl
             | [ H : context[addB #0 _] |- _ ] => rewrite add0B in H
           end. }
  { by rewrite addB_decB_incB. }
Qed.

Local Ltac t_after_specapply := ssimpl; try reflexivity; rewrite /ConditionIs/OSZCP/stateIsAny/stateIs; cbv beta; ssimpl; try reflexivity; sbazooka.

Local Ltac do_code_unfolder :=
  rewrite /makeBOP.

Local Ltac check_eip_hyp_and_do hyp :=
  let G := match goal with |- ?G => constr:(G) end in
  let T := type_of hyp in
  check_eips_match G T;
    setoid_rewrite hyp;
    do_code_unfolder;
    try by finish_logic_with sbazooka.

Local Ltac prepare_basic_goal_for_spec :=
  rewrite /makeBOP/makeMOV;
  autorewrite with push_at;
  do ?(idtac;
       match goal with
         | [ |- _ |-- basic _ (LOCAL _; _) _ ] => apply basic_local => ?
       end);
  rewrite /basic;
  do ?[ progress subst
      | progress specintros => *
      | progress unfold_program ].

Definition output_n_prog (pbody : program) (n : nat)
  := (LOCAL LOOP;
      LOCAL END;
      LOOP:;;
        CMP ECX, (0:DWORD);;
        JCC CC_Z true END;;
        pbody;;
        DEC ECX;;
        JMP LOOP;;
        END:;).

