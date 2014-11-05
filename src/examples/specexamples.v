Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.safe x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.macros.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor.
Require Import x86proved.spectac x86proved.basicspectac.
Require Import x86proved.common_tactics x86proved.chargetac x86proved.common_definitions.
Require Import Coq.Setoids.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Generalizable All Variables.

Local Open Scope instr_scope.

(* Example: It is safe to sit forever in a tight loop. *)
Example safe_loop (p q: DWORD) :
  |-- safe @ (EIP ~= p ** p -- q :-> JMP p).
Proof.
  apply: spec_lob.
  superspecapply *. 
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
  unfold_program. specintros => _ <- <-.  
  autorewrite with push_at.
  apply: limplAdj. apply: landL1. 
  etransitivity; [apply safe_loop|]. finish_logic. 
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
  by rewrite addIsIterInc/iter.
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
        CMP ECX, 0;;
        JCC CC_Z true END;;
        pbody;;
        DEC ECX;;
        JMP LOOP;;
        END:;).

(*
(** Example: We can observe the output of any given constant, n times *)
Example safe_loop_n P (pbody : program) O (n : nat) d
        (small_enough : nat -> Prop)
        (is_small : forall n, small_enough (n.+1) -> small_enough n)
        (small_is_good : forall n, small_enough n -> (#(n.+1) == @fromNat n32 0) = false)
        (Hn : small_enough n)
        (H : forall n, small_enough n -> |--basic (ECX ~= #(n.+1) ** AL ~= d ** P (n.+1) ** OSZCP?) pbody (O (n.+1)) (ECX ~= #(n.+1) ** AL ~= d ** P n ** OSZCP?))
: |-- (basic (ECX ~= #n ** AL ~= d ** P n)
             (output_n_prog pbody n)
             (rollOP n O)
             (ECX ~= #0 ** AL ~= d ** P 0))
      @ OSZCP?.
Proof.
  unfold output_n_prog.
  prepare_basic_goal_for_spec.
  induction n.
  { 
    do? [ progress rewrite ?subB0 ?eq_refl /OSZCP/ConditionIs
        | check_goal_eips_match; by finish_logic_with sbazooka
        | specapply * ]. }
  { specialize (IHn (is_small _ Hn)).
    specialize (small_is_good _ (is_small _ Hn)).
    specialize (H _ (is_small _ Hn)).
    (** Get the instance so that [specapply *] picks it up *)
    instrrule remember H. 
    do ![ progress rewrite ?subB0 ?eq_refl ?small_is_good ?rollOP_defS ?catOPA ?decB_fromSuccNat /ConditionIs
        | rewrite /OSZCP/stateIsAny; specintros => *
        | progress change (false == true) with false; cbv iota
        | solve [ check_eip_hyp_and_do IHn ]
        | specapply *; first by t_after_specapply ]. admit. }
Qed.

Example safe_loop_n_const P (pbody : program) O (n : nat) d
        (small_enough : nat -> Prop)
        (is_small : forall n, small_enough (n.+1) -> small_enough n)
        (small_is_good : forall n, small_enough n -> (#(n.+1) == @fromNat n32 0) = false)
        (Hn : small_enough n)
        (H : forall n, small_enough n -> |--basic (ECX ~= #(n.+1) ** AL ~= d ** P ** OSZCP?) pbody O (ECX ~= #(n.+1) ** AL ~= d ** P ** OSZCP?))
: |-- (basic (ECX ~= #n ** AL ~= d ** P)
             (output_n_prog pbody n)
             (repOP n O)
             (ECX ~= #0 ** AL ~= d ** P))
      @ OSZCP?.
Proof.
  rewrite repOP_rollOP.
  eapply (@safe_loop_n (fun _ => P) pbody (fun _ => O) n d);
    eassumption.
Qed.

Section helper.
  (** We need these opaque to speed up setoid rewriting. *)
  Local Opaque lforall limpl illater spec_at spec_reads.
  Lemma safe_loop_forever_later_helper_faster `{@ILogic Frm ILOps'}
        {T1 T2 T3 S1 c1 S2 c2 R}
        (H0 : |-- ((Forall (x : T1) (y : T2) (z : T3 x y), ((((*|>*)S1) @ c1 -->> (|>S2 x y z) @ c2 x y z)))
                     -->>
                     (Forall (x : T1) (y : T2) (z : T3 x y), ((S1 @ c1 -->> S2 x y z @ c2 x y z)))) <@ R)
  : |-- |>(Forall (x : T1) (y : T2) (z : T3 x y), ((S1 @ c1 -->> S2 x y z @ c2 x y z) <@ R))
        -->>
        (Forall (x : T1) (y : T2) (z : T3 x y), ((S1 @ c1 -->> S2 x y z @ c2 x y z) <@ R)).
  Proof.
    repeat match goal with
             | _ => progress autorewrite with push_later; [|by typeclasses eauto..]
             | [ |- context[|>(Forall _ : _, _)] ] => setoid_rewrite spec_later_forall
             | [ |- context[|>(_ -->> _)] ]        => setoid_rewrite spec_later_impl
             | [ |- context[|>(_ @ _)] ]           => setoid_rewrite <- spec_at_later
             | [ |- context[|>(_ <@ ?R)] ]         => setoid_rewrite (fun S => proj2 (@spec_reads_later S R)) (* this case is slow *)
             | _ => progress setoid_rewrite <- spec_reads_forall
             | _ => progress setoid_rewrite <- spec_reads_impl
           end.
    setoid_rewrite <- (spec_later_weaken S1).
    exact H0.
  Qed.
End helper.

Definition loop_forever_prog (pbody : program)
  := (LOCAL LOOP;
      LOOP:;;
          pbody;;
          JMP LOOP).

(** Example: We can observe the output of any given code, infinitely many times *)
(** TODO(t-jagro): automate this proof more *)
Example safe_loop_forever (PP : nat -> SPred -> Prop) (pbody : program) (O : nat -> OPred)
        (transition : forall P n, PP n P -> SPred)
        (transition_correct : forall P n (H : PP n P), PP (n.+1) (transition P n H))
        (H : forall P n (H' : PP n P) (Q := transition P n H'), PP (S n) Q -> |--basic P pbody (O n) Q)
        (P0 : SPred) (start : nat) (H0 : PP start P0)
: |-- (basic P0
                   (loop_forever_prog pbody)
                   (roll_starOP O start)
                   lfalse).
Proof.
  unfold loop_forever_prog.
  prepare_basic_goal_for_spec.
  lrevert H0.
  lrevert P0.
  lrevert start.
  apply spec_lob_context.
  apply landAdj.
  apply safe_loop_forever_later_helper_faster.
  do !setoid_rewrite lforall_limpl_commute.
  let H := match goal with |- |-- ((?A -->> ?B) -->> ?A -->> ?C) <@ _ => constr:(triple_limpl A B C) end in
  setoid_rewrite <- H.
  specintros => start Pstart PPstart.
  specialize (transition_correct Pstart start PPstart).

  (** The body code *)
  specapply H; clear H; do [ eassumption |  by apply catOP_O_roll_starOP_O' | ]. 
  by ssimpl. 

  (** The jump code *)
  specapply JMP_I_rule. by ssimpl.
  simpl OPred_pred.

  finish_logic_with sbazooka.
Qed.

Example safe_loop_forever_state_machine state (transition : state -> state)
        (P : state -> SPred) (pbody : program) (O : state -> OPred)
        (H : forall s, |--basic (P s) pbody (O s) (P (transition s)))
        (start : state) (state_n := fun n => rep_apply n transition start)
: |-- (basic (P start)
                   (loop_forever_prog pbody)
                   (roll_starOP (fun n => O (state_n n)) 0)
                   lfalse).
Proof.
  exact (@safe_loop_forever
           (fun n => eq (P (state_n n)))
           pbody
           (fun n => O (state_n n))
           (fun _ n _ => P (state_n (S n)))
           (fun _ _ _ => reflexivity _)
           (fun P0 n H0 _ => @eq_rect _ _ (fun P0 => |--basic P0 pbody (O (state_n n)) (P (state_n n.+1))) (H _) _ H0)
           (P start)
           0
           (reflexivity _)).
Qed.

Example safe_loop_forever_constant P (pbody : program) O
        (H : |--basic P pbody O P)
: |-- basic P (loop_forever_prog pbody) (starOP O) lfalse.
Proof.
  rewrite <- (roll_starOP__starOP 0 O).
  exact (@safe_loop_forever (fun _ => eq P) pbody (fun _ => O) (fun _ _ _ => P) (fun _ _ _ => reflexivity _)
                             (fun P0 _ PeqP0 _ => @eq_rect _ _ (fun P0 => |--basic P0 pbody O P) H _ PeqP0) P 0
                             (reflexivity _)).
Qed.

Example loop_forever_one al
: |-- (basic (AL ~= al)
                   (MOV AL, (#1 : DWORD);;
                    loop_forever_prog (OUT #0, AL))
                   (starOP (outOP (zeroExtend n8 (#0 : BYTE)) (#1 : BYTE)))
                   lfalse).
Proof.
  basic apply loopy *.
  change (@low 24 8 (@fromNat n32 1)) with (@fromNat n8 1).
  eapply safe_loop_forever_constant.
  basic apply *.
Qed.

Definition echo_once in_c out_c :=
  (IN in_c, AL;;
   OUT out_c, AL).

Definition echo_once_clean (al in_c out_c : BYTE) :=
  (echo_once in_c out_c;;
   MOV AL, al).

Definition echo_once_OP_helper (in_c out_c : BYTE) v := catOP (inOP (zeroExtend n8 in_c) v) (outOP (zeroExtend n8 out_c) v).

Example safe_echo_once al in_c out_c
: |-- Forall v, basic (AL ~= al)
                      (echo_once in_c out_c)
                      (echo_once_OP_helper in_c out_c v)
                      (AL ~= v).
Proof.
  specintros => v. rewrite /echo_once/echo_once_OP_helper.
  basic apply *.
  basic apply *.
Qed.

Instance: forall in_c out_c, instrrule (echo_once in_c out_c) := fun in_c out_c al => @safe_echo_once al in_c out_c.

Example safe_echo_once_clean (al in_c out_c : BYTE) v
: |-- (basic (AL ~= al)
             (echo_once_clean al in_c out_c)
             (echo_once_OP_helper in_c out_c v)
             (AL ~= al)).
Proof.
  rewrite /echo_once_clean/echo_once_OP_helper.
  basic apply *.
  basic apply *.
  by rewrite low_catB.
Qed.

Instance: forall al in_c out_c, instrrule (echo_once_clean al in_c out_c) := @safe_echo_once_clean.

Definition echo_n al in_c out_c n := output_n_prog (echo_once_clean al in_c out_c) n.

Definition list_to_in_out (in_c out_c : BYTE) ls
  := [seq catOP (inOP (zeroExtend n8 in_c) v) (outOP (zeroExtend n8 out_c) v) | v <- ls ].

(** TODO: clean up this proof *)
Example safe_echo_n in_c out_c n d
        (small_enough : nat -> Prop)
        (is_small : forall n, small_enough (n.+1) -> small_enough n)
        (small_is_good : forall n, small_enough n -> (#(n.+1) == @fromNat n32 0) = false)
        (Hn : small_enough n)
: |-- Forall ls (pf : n.+1 < size ls),
  (basic (ECX ~= #n ** AL ~= d)
         (echo_n d in_c out_c n)
         (rollOP n (fun k => nth empOP (list_to_in_out in_c out_c ls) (k.-1)))
         (ECX ~= #0 ** AL ~= d)
         @ OSZCP?).
Proof.
  specintros => ls pf.
  rewrite /echo_n.
  pose proof (@safe_loop_n (fun _ => empSP) (echo_once_clean d in_c out_c) (fun k => nth empOP (list_to_in_out in_c out_c ls) (k.-1)) n d (fun k => small_enough k /\ k < n.+1)) as H.
  cbv beta in H.
  rewrite -> !empSPR in H.
  apply H; [ by intuition | by intuition | by intuition | ].
  move => n' [ Hsmall Hle ].
  clear H.
  attempt basic apply *.
  rewrite /echo_once_OP_helper.
  rewrite /list_to_in_out.
  erewrite nth_map; first by reflexivity.
  by erewrite ltn_trans; try eassumption.
  Grab Existential Variables.
  exact #0.
Qed.

(* Example: It is safe to sit in a less tight loop forever. *)
Example safe_loop_io P c O (H : |-- basic P c O P @ (EAX? ** OSZCP?))
: |-- basic (EAX? ** OSZCP? ** P) (while (TEST EAX, EAX) CC_O false c) (starOP O) lfalse.
Proof.
  basic apply (while_rule_ind
                 (transition_body := @id unit)
                 (P := fun _ => P ** EAX? ** OF? ** SF? ** ZF? ** CF? ** PF?)
                 (I_state := fun _ _ => P ** EAX? ** SF? ** ZF? ** CF? ** PF?)
                 (I_logic := fun _ b => b == false)
                 (Otest := fun _ => empOP)
                 (Obody := fun _ => O)
                 (O_after_test := fun _ => default_PointedOPred (starOP O))
                 (O := fun _ => default_PointedOPred (starOP O))
                 (Q := fun _ => lfalse)) => //= *.
  { by ssimpl. } 
  { setoid_rewrite ->starOP_def at -1. by apply lorR2. }
  { specintros => *; basic apply H. }
  { rewrite /stateIsAny; specintros => *; basic apply *. }
Qed.
*)