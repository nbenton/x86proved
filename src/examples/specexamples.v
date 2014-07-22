Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.opred x86proved.septac x86proved.spec x86proved.obs x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.macros.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor.
Require Import x86proved.spectac x86proved.basicspectac.
Require Import x86proved.common_tactics x86proved.chargetac.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Generalizable All Variables.

Local Open Scope instr_scope.

(* Example: It is safe to sit forever in a tight loop. *)
Example safe_loop (p q: DWORD) (O : PointedOPred) :
  |-- obs O @ (EIP ~= p ** p -- q :-> JMP p).
Proof.
  apply: spec_lob.
  have H := @JMP_I_loopy_rule p p q.
  apply (lforallE_spec O) in H. cbv beta in H.
  rewrite ->spec_reads_entails_at in H; [|apply _].
  autorewrite with push_at in H. apply landAdj in H.
  etransitivity; [|apply H]. apply: landR; [sbazooka | reflexivity].
Qed.

(* We can package up jumpy code in a triple by using labels. *)
Example basic_loop:
  |-- loopy_basic empSP (LOCAL l; l:;; JMP l) empOP lfalse.
Proof.
  rewrite /loopy_basic. specintros => i j O'.
  unfold_program. specintros => _ _ <- <-.
  rewrite /spec_reads. specintros => code Hcode.
  autorewrite with push_at.
  apply: limplAdj. apply: landL1. rewrite -> Hcode.
  etransitivity; [apply safe_loop|]. rewrite ->empOPL. cancel2. reflexivity. eexists _. split; by ssimpl.
Qed.

(* Show off the sequencing rule for [basic]. *)
Example basic_inc3 x:
  |-- basic (EAX ~= x)
            (INC EAX;; INC EAX;; INC EAX) empOP
            (EAX ~= x +# 3) @ OSZCP?.
Proof.
  autorewrite with push_at. rewrite /stateIsAny.
  specintros => o s z c p.
  try_basicapply INC_R_rule. rewrite /OSZCP; sbazooka.
  try_basicapply INC_R_rule. rewrite /OSZCP; sbazooka.
  try_basicapply INC_R_rule. rewrite /OSZCP; sbazooka.
  rewrite /OSZCP addIsIterInc/iter; sbazooka.
Qed.

Example incdec_while c a:
  |-- loopy_basic
    (ECX ~= c ** EAX ~= a)
    (
      while (TEST ECX, ECX) CC_Z false (
        DEC ECX;;
        INC EAX
      )
    ) empOP
    (ECX ~= #0 ** EAX ~= addB c a)
    @ OSZCP?.
Proof.
  autorewrite with push_at.
  set (I := fun b => Exists c', Exists a',
    (c' == #0) = b /\\ addB c' a' = addB c a /\\
    ECX ~= c' ** EAX ~= a' **
    OF? ** SF? ** CF? ** PF?).
  eapply basic_basic_context; first apply (while_rule_ro (I:=I));
      first 2 last.
  - reflexivity.
  - subst I. rewrite /stateIsAny/ConditionIs. sbazooka.
  - reflexivity.
  - subst I; cbv beta. sdestructs => c' a' Hzero Hadd.
    rewrite ->(eqP Hzero) in *. rewrite add0B in Hadd.
    subst a'. rewrite /ConditionIs/stateIsAny. by sbazooka.
  - specintros => b1 b2. subst I; cbv beta. specintros => c' a' Hzero Hadd.
    eapply basic_basic. exact (TEST_self_rule (v:= c')).
    + rewrite /ConditionIs/stateIsAny. by sbazooka.
    rewrite /OSZCP/ConditionIs/stateIsAny. by sbazooka.
  - subst I; cbv beta. specintros => c' a' Hzero Hadd.
    rewrite /stateIsAny. specintros => fo fs fc fp.
    try_basicapply DEC_R_rule. + by rewrite /OSZCP/ConditionIs; ssimpl.
    try_basicapply INC_R_rule. + by rewrite addB_decB_incB.
    rewrite /OSZCP/ConditionIs.
    sbazooka.
Qed.


(** TODO(t-jagro): Move these tactics to a better location. *)
Ltac specexamples_specapply rule tac :=
  let H := fresh in
  pose proof rule as H;
    unfold specAtDstSrc, specAtRegMemDst in H;
    cbv beta in H;
    specapply H; clear H; first tac.

Ltac specintro_stateIsAny reg := let regq := constr:(reg?) in rewrite /regq; specintros => *; rewrite -/regq.
Ltac specintros_OSZCP :=
  specintro_stateIsAny OF; specintro_stateIsAny SF; specintro_stateIsAny ZF; specintro_stateIsAny CF; specintro_stateIsAny PF.

Ltac do_code_rule_loopless code matcher :=
  let tac := (ssimpl; try reflexivity; rewrite /OSZCP/DWORDorBYTEregIs/stateIsAny/stateIs; cbv beta; ssimpl; try reflexivity; sbazooka) in
  lazymatch code with
    | BOP ?d OP_CMP ?ds          => let ecx := get_post_reg ECX in specexamples_specapply (@CMP_rule d ds ecx) ltac:(by tac)
    | JZ ?a                      => specexamples_specapply (@JZ_rule a) ltac:(by tac)
    | JMP (JmpTgtI (mkTgt ?a))   => specexamples_specapply (@JMP_I_rule a) ltac:(by tac)
    | UOP ?d OP_INC ?a           => let ecx := get_post_reg ECX in specintros_OSZCP; specexamples_specapply (@INCDEC_rule d true a ecx) ltac:(by tac)
    | UOP ?d OP_DEC ?a           => let ecx := get_post_reg ECX in specintros_OSZCP; specexamples_specapply (@INCDEC_rule d false a ecx) ltac:(by tac)
    | _                          => let rule := matcher code in specexamples_specapply rule ltac:(by tac)
  end.


Ltac do_code_unfolder :=
  rewrite /makeUOP/makeBOP.

Ltac do_code_loopless' matcher :=
  do_code_unfolder;
  let G := match goal with |- ?G => constr:(G) end in
  let x := get_eip_code G in
  do_code_rule_loopless x matcher.

Ltac do_code_loopless_with matcher intertac :=
  do !(do_code_loopless' matcher; intertac).

Ltac check_goal_eips_match :=
  let pre_eip := get_pre_reg EIP in
  let post_eip := get_post_reg EIP in
  constr_eq pre_eip post_eip.

Ltac do_code_loopless :=
  do_code_loopless_with
    ltac:(fun code => fail)
    ltac:(rewrite ?subB0 ?eq_refl;
          try (check_goal_eips_match; try by finish_logic_with sbazooka)).

Ltac check_eip_hyp_and_do hyp :=
  let G := match goal with |- ?G => constr:(G) end in
  let T := type_of hyp in
  check_eips_match G T;
    setoid_rewrite hyp;
    do_code_unfolder;
    try by finish_logic_with sbazooka.

Ltac prepare_basic_goal_for_spec :=
  autorewrite with push_at;
  do ?(idtac;
       match goal with
         | [ |- _ |-- parameterized_basic _ (LOCAL _; _) _ _ ] => apply basic_local => ?
       end);
  rewrite /parameterized_basic;
  do ?[ progress subst
      | progress specintros => *
      | progress unfold_program ].


(** Example: We can observe the output of any given constant, n times *)
Example safe_loop_n P (pbody : program) O (n : nat) d
        (small_enough : nat -> Prop)
        (is_small : forall n, small_enough (n.+1) -> small_enough n)
        (small_is_good : forall n, small_enough n -> (#(n.+1) == @fromNat n32 0) = false)
        (Hn : small_enough n)
        (H : forall n, small_enough n -> |--basic (ECX ~= #(n.+1) ** BYTEregIs AL d ** P (n.+1) ** OSZCP?) pbody (O (n.+1)) (ECX ~= #(n.+1) ** BYTEregIs AL d ** P n ** OSZCP?))
: |-- (basic (ECX ~= #n ** BYTEregIs AL d ** P n)
             (LOCAL LOOP;
              LOCAL END;
               LOOP:;;
               CMP ECX, 0;;
               JCC CC_Z true END;;
               pbody;;
               DEC ECX;;
               JMP LOOP;;
               END:;)
             (rollOP n O)
             (ECX ~= #0 ** BYTEregIs AL d ** P 0))
      @ OSZCP?.
Proof.
  prepare_basic_goal_for_spec.
  induction n.
  { do_code_loopless. }
  { specialize (IHn (is_small _ Hn)).
    specialize (small_is_good _ (is_small _ Hn)).
    specialize (H _ (is_small _ Hn)).
    do_code_loopless_with
      ltac:(fun code =>
              match code with
                | pbody => constr:(H)
              end)
      ltac:(rewrite ?subB0 ?eq_refl ?small_is_good ?catOPA ?decB_fromSuccNat /rollOP-/rollOP;
            try check_eip_hyp_and_do IHn). }
Qed.

Example safe_loop_n_const P (pbody : program) O (n : nat) d
        (small_enough : nat -> Prop)
        (is_small : forall n, small_enough (n.+1) -> small_enough n)
        (small_is_good : forall n, small_enough n -> (#(n.+1) == @fromNat n32 0) = false)
        (Hn : small_enough n)
        (H : forall n, small_enough n -> |--basic (ECX ~= #(n.+1) ** BYTEregIs AL d ** P ** OSZCP?) pbody O (ECX ~= #(n.+1) ** BYTEregIs AL d ** P ** OSZCP?))
: |-- (basic (ECX ~= #n ** BYTEregIs AL d ** P)
             (LOCAL LOOP;
              LOCAL END;
               LOOP:;;
               CMP ECX, 0;;
               JCC CC_Z true END;;
               pbody;;
               DEC ECX;;
               JMP LOOP;;
               END:;)
             (repOP n O)
             (ECX ~= #0 ** BYTEregIs AL d ** P))
      @ OSZCP?.
Proof.
  rewrite repOP_rollOP.
  eapply (@safe_loop_n (fun _ => P) pbody (fun _ => O) n d);
    eassumption.
Qed.

Example safe_loop_forever P (pbody : program) O
        (H : |--basic P pbody O P)
: |-- loopy_basic P (LOCAL LOOP;
                     LOOP:;;
                         pbody;;
                         JMP LOOP) (starOP O) lfalse.
Proof.
  prepare_basic_goal_for_spec.
  apply spec_lob_context.
  apply landAdj.
  autorewrite with push_later; [|by typeclasses eauto..].
  setoid_rewrite <- spec_reads_impl.
  let H := match goal with |- |-- ((illater ?H @ _ -->> _) -->> _ -->> _) <@ _ => constr:(H) end in
  setoid_rewrite <- (spec_later_weaken H).
  let H := match goal with |- |-- ((?A -->> ?B) -->> ?A -->> ?C) <@ _ => constr:(triple_limpl A B C) end in
  setoid_rewrite <- H.
  specapply H; clear H; do [ by ssimpl | by apply catOP_O_starOP_O' | idtac ]; [].
  specapply JMP_I_loopy_rule; first by ssimpl.
  simpl OPred_pred.
  finish_logic_with sbazooka.
Qed.
