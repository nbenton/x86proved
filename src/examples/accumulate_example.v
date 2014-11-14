(** * Example of an accumulator *)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple Ssreflect.ssrfun.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.opred x86proved.spec x86proved.obs x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.macros.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor.
Require Import x86proved.spectac x86proved.basicspectac.
Require Import x86proved.common_tactics x86proved.chargetac x86proved.common_definitions.
Require Import x86proved.x86.ioaction.
Require Coq.Lists.Streams.
Require Import Coq.Setoids.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Generalizable All Variables.

Local Open Scope instr_scope.

Local Ltac t_accum' coq_test__is_finished fin_tac :=
  idtac;
  match goal with
    | _ => done
    | _ => evar_safe_syntax_unify_reflexivity
    | [ H : ?x = ~~?x |- _ ] => by destruct (@Bool.no_fixpoint_negb x (symmetry H))
    | [ H : ~~?x = ?x |- _ ] => by destruct (@Bool.no_fixpoint_negb x H)
    | [ H : is_true (?x == ?y) |- _ ] => move/eqP in H
    | [ H : context[?x == ?x] |- _ ] => rewrite eq_refl in H
    | _ => progress intros
    | _ => progress simpl in *
    | _ => progress destruct_head_hnf sigT
    | _ => progress destruct_head_hnf prod
    | _ => progress ssimpl
    | _ => progress hyp_destruct_atomic_in_match'
    | _ => progress destruct_atomic_in_match'
    | _ => progress specintros => *
    | _ => basic apply *
    | [ |- _ |-- parameterized_basic _ _ _ (lexists _) ] => eapply basic_post_exists
    | [ |- _ |-- parameterized_basic _ _ _ (_ /\\ _) ] => eapply basic_post_exists
    | [ H : context[if coq_test__is_finished ?x then _ else _],
            H' : context[only_last coq_test__is_finished ?x ?xs] |- _ ] => atomic xs; destruct xs; simpl only_last in H'
    | [ H : context[if coq_test__is_finished ?x then _ else _] |- _ ] => atomic x; destruct (coq_test__is_finished x)
    | [ |- _ |-- lexists _ ] => eapply lexistsR; by fin_tac
  end.

Local Ltac t_accum coq_test__is_finished := do ?t_accum' coq_test__is_finished ltac:(t_accum coq_test__is_finished).

(** Example: We can accumulate input while it satisfies some condition *)
(** This could be generalized so that the hypotheses only need to talk
    about things in the image of [initial] under repeated
    [accumulate]... *)
(** This version doesn't suffer from an off-by-one-error. *)
Lemma accumulator_while_rule ptest cond value pbody
      {T ioT}
      (P : T -> ioT -> SPred) (I : T -> ioT -> bool -> SPred) (accumulate : T -> ioT -> T)
      (Otest : T -> ioT -> PointedOPred)
      (Obody : T -> ioT -> PointedOPred)
      (coq_test__is_finished : ioT -> bool)
      S
      (H_test : forall initial x xs,
                  only_last coq_test__is_finished x xs
                  -> S
                       |-- (loopy_basic (P initial x) ptest
                                        (Otest initial x)
                                        (I initial x
                                           ((if coq_test__is_finished x then ~~ value else value) : bool) **
                                           ConditionIs cond
                                           ((if coq_test__is_finished x then ~~ value else value) : bool))))
      (H_body : forall initial x xs,
                  xs <> nil
                  -> only_last coq_test__is_finished x xs
                  -> S
                       |-- (loopy_basic (I initial x value ** ConditionIs cond value) pbody
                                        (Obody (accumulate initial x) (head x xs))
                                        (P (accumulate initial x) (head x xs))))
: S |-- (Forall initial x xs (pf1 : only_last coq_test__is_finished x xs),
         (loopy_basic (P initial x)
                      (while ptest cond value pbody)
                      (snd (foldl (fun xy v =>
                                     (accumulate (fst xy) v,
                                      catOP (snd xy) (catOP (Obody (fst xy) v) (Otest (fst xy) v))))
                                  (accumulate initial x, Otest initial x : OPred)
                                  xs))
                      (I (foldl accumulate initial (drop_last x xs)) (last x xs) (~~value) ** ConditionIs cond (~~value)))).
Proof.
  specintros => initial x xs pf.
  pose (existT (fun init_x_xs => only_last _ (snd (fst init_x_xs)) (snd init_x_xs)) (initial, x, xs) pf) as ixsp.
  change initial with (fst (fst (projT1 ixsp))).
  change x with (snd (fst (projT1 ixsp))).
  change xs with (snd (projT1 ixsp)).
  clearbody ixsp.
  clear x xs pf initial.
  let O := match goal with |- _ |-- parameterized_basic _ _ ?O _ => constr:(O) end in
  change O with (OPred_pred (default_PointedOPred O)).
  lrevert ixsp.
  eapply @while_rule_ind
  with (I_logic := fun ixsp b => let x := snd (fst (projT1 ixsp)) in (if coq_test__is_finished x then ~~value else value) == b)
         (Otest := fun ixsp => let initial := fst (fst (projT1 ixsp)) in
                               let x := snd (fst (projT1 ixsp)) in
                               Otest initial x)
         (Obody := fun ixsp => let initial := fst (fst (projT1 ixsp)) in
                               let x := snd (fst (projT1 ixsp)) in
                               let xs := snd (projT1 ixsp) in
                               Obody (accumulate initial x) (nth x xs 0))
         (I_state := fun ixsp => let initial := fst (fst (projT1 ixsp)) in
                                 let x := snd (fst (projT1 ixsp)) in
                                 I initial x)
         (transition_body := fun ixsp : sigT (fun init_x_xs : T * ioT * seq ioT => only_last coq_test__is_finished (snd (fst init_x_xs)) (snd init_x_xs))
                             => let initial := fst (fst (projT1 ixsp)) in
                                let x := snd (fst (projT1 ixsp)) in
                                let xs := snd (projT1 ixsp) in
                                existT (fun init_x_xs : T * ioT * seq ioT => only_last coq_test__is_finished (snd (fst init_x_xs)) (snd init_x_xs))
                                       (accumulate initial x, head x xs, behead xs)
                                       (only_last_behead _ _ _ (projT2 ixsp)))
         (O_after_test := fun ixsp => let initial := fst (fst (projT1 ixsp)) in
                                      let x := snd (fst (projT1 ixsp)) in
                                      let xs := snd (projT1 ixsp) in
                                      default_PointedOPred
                                        (snd (foldl (fun xy v =>
                                                       (accumulate (fst xy) v,
                                                        catOP (snd xy) (catOP (Obody (fst xy) v) (Otest (fst xy) v))))
                                                    (accumulate initial x, empOP)
                                                    xs)));
    simpl projT1; simpl projT2; simpl fst; simpl snd.
  { specintros => *; destruct_head_hnf sigT; simpl in *.
      by attempt basic apply H_test; eassumption. }
  { specintros => *; destruct_head_hnf sigT; destruct_head_hnf prod; simpl in *.
    attempt basic apply H_body; try (reflexivity || assumption).
    t_accum coq_test__is_finished. }
  { t_accum coq_test__is_finished.
    pose (fun (x : T) (v : ioT) => catOP (Obody x v) (Otest x v)) as f.
    change (fun (xy : T * OPred) (v : ioT) =>
              (accumulate (fst xy) v,
               catOP (snd xy) (catOP (Obody (fst xy) v) (Otest (fst xy) v))))
    with (fun xy v => (accumulate (fst xy) v, catOP (snd xy) (f (fst xy) v))).
    rewrite -> !foldl_catOP_to_functions.
    rewrite <- !catOP_foldl_helper'.
    by rewrite ?catOPA ?empOPL ?empOPR. }
  { t_accum coq_test__is_finished.
    pose (fun (x : T) (v : ioT) => catOP (Obody x v) (Otest x v)) as f.
    change (fun (xy : T * OPred) (v : ioT) =>
              (accumulate (fst xy) v,
               catOP (snd xy) (catOP (Obody (fst xy) v) (Otest (fst xy) v))))
    with (fun xy v => (accumulate (fst xy) v, catOP (snd xy) (f (fst xy) v))).
    rewrite -> !foldl_catOP_to_functions.
    rewrite <- !catOP_foldl_helper'.
    by rewrite ?catOPA ?empOPL ?empOPR. }
  { t_accum coq_test__is_finished. }
  { t_accum coq_test__is_finished. }
  { t_accum coq_test__is_finished. }
Qed.



Lemma accumulator_while_rule_state_independent_io ptest cond value pbody
      {T ioT}
      (P : T -> ioT -> SPred) (I : T -> ioT -> bool -> SPred) (accumulate : T -> ioT -> T)
      (Otest : ioT -> PointedOPred)
      (Obody : ioT -> PointedOPred)
      (coq_test__is_finished : ioT -> bool)
      S
      (H_test : forall initial x xs,
                  only_last coq_test__is_finished x xs
                  -> S
                       |-- (loopy_basic (P initial x) ptest
                                        (Otest x)
                                        (I initial x
                                           ((if coq_test__is_finished x then ~~ value else value) : bool) **
                                           ConditionIs cond
                                           ((if coq_test__is_finished x then ~~ value else value) : bool))))
      (H_body : forall initial x xs,
                  xs <> nil
                  -> only_last coq_test__is_finished x xs
                  -> S
                       |-- (loopy_basic (I initial x value ** ConditionIs cond value) pbody
                                        (Obody (head x xs))
                                        (P (accumulate initial x) (head x xs))))
: S |-- (Forall initial x xs (pf1 : only_last coq_test__is_finished x xs),
         (loopy_basic (P initial x)
                      (while ptest cond value pbody)
                      (catOP (Otest x)
                             (foldr catOP empOP (map (fun v => catOP (Obody v) (Otest v)) xs)))
                      (I (foldl accumulate initial (drop_last x xs)) (last x xs) (~~value) ** ConditionIs cond (~~value)))).
Proof.
  specintros => *.
  rewrite /= foldr_map.
  rewrite <- foldl_fun_catOP_foldr.
  attempt strict basic apply (@accumulator_while_rule
                                ptest cond value pbody
                                T ioT
                                P I accumulate
                                (fun _ => Otest)
                                (fun _ => Obody)
                                coq_test__is_finished
                                S
                                H_test
                                H_body); try assumption;
  [].
  rewrite <- foldl_fun_catOP_pull.
  etransitivity; [ | erewrite <- snd_foldl; reflexivity ]; reflexivity.
Qed.


Definition accumulate_prog (ptest: program)
           (cond: Condition) (value: bool)
           (pbody: program) in_ch
  := (IN in_ch, AL;;
      while ptest cond value (
        pbody;;
        IN in_ch, AL
     )).

Example accumulate_until_prog_safe ptest cond value pbody c
        {T}
        (P : T -> SPred) (I : T -> BYTE -> bool -> SPred) (accumulate : T -> BYTE -> T)
        (test_finished : BYTE -> bool)
        S al
        (H_test : forall initial x xs,
                    only_last test_finished x xs
                    -> S
                         |-- (loopy_basic (P initial ** AL ~= x)
                                          ptest
                                          empOP
                                          (I initial x
                                             ((if test_finished x then ~~ value else value) : bool) **
                                             ConditionIs cond
                                             ((if test_finished x then ~~ value else value) : bool))))
        (H_body : forall initial x xs,
                    xs <> nil
                    -> only_last test_finished x xs
                    -> S
                         |-- (loopy_basic (I initial x value ** ConditionIs cond value) pbody
                                          empOP
                                          (P (accumulate initial x) ** AL?)))
: S |-- (Forall initial x xs (pf1 : only_last test_finished x xs),
         (loopy_basic (P initial ** AL ~= al)
                      (accumulate_prog ptest cond value pbody c)
                      (foldr catOP empOP (map (inOP (zeroExtend n8 c)) (x::xs)))
                      (I (foldl accumulate initial (drop_last x xs)) (last x xs) (~~value) ** ConditionIs cond (~~value)))).
Proof.
  specintros => initial x xs pf.
  simpl.
  rewrite /accumulate_prog.
  basic apply *; simpl OPred_pred.
  attempt strict basic apply (@accumulator_while_rule_state_independent_io
                                ptest cond value (pbody;; IN c, AL) T BYTE
                                (fun initial x => AL ~= x ** P initial)
                                I
                                accumulate
                                (fun _ => default_PointedOPred empOP)
                                (fun v => default_PointedOPred (inOP (zeroExtend n8 c) v))
                                test_finished
                                S).
  { simpl OPred_pred; rewrite empOPL.
    apply foldr_catOP_map_respects_lentails => *.
    by rewrite empOPR. }
  { assumption. }
  { basic apply H_body; try eassumption.
    rewrite /stateIsAny; specintros => *.
    basic apply *. }
  { basic apply H_test; eassumption. }
Qed.

Definition accumulate_until_value_prog (value:BYTE)
           (pbody: program) in_ch
  := accumulate_prog (CMP AL, value) CC_Z false pbody in_ch.

(** TODO: put in the reasoning that [last x xs == value]; we'll need a lemma relating [last] and [only_last] *)
Example accumulate_until_value_prog_safe value
        {T} (P : T -> SPred)
        (accumulate : T -> BYTE -> T)
        pbody ch o s z c p
        S al
        (H_body : forall initial x xs,
                    xs <> nil
                    -> only_last (fun t : BYTE => t == (value : BYTE)) x xs
                    -> S
                         |-- (loopy_basic (P initial ** AL ~= x ** OF? ** SF? ** ZF ~= false ** CF? ** PF?) pbody
                                          empOP
                                          (P (accumulate initial x) ** AL? ** OF? ** SF? ** ZF? ** CF? ** PF?)))
: S |-- (Forall initial x xs (pf1 : only_last (fun t : BYTE => t == value) x xs),
         (loopy_basic (P initial ** AL ~= al ** OSZCP o s z c p)
                      (accumulate_until_value_prog (value) pbody ch)
                      (foldr catOP empOP (map (inOP (zeroExtend n8 ch)) (x::xs)))
                      (P (foldl accumulate initial (drop_last x xs)) ** AL ~= (last x xs) ** OF? ** SF? ** ZF ~= true ** CF? ** PF?))).
Proof.
  rewrite /OSZCP. specintros => *.
  rewrite /accumulate_until_value_prog.
  basic apply (fun ptest cond value' pbody ch
                => @accumulate_until_prog_safe ptest cond value' pbody ch T
                                               (fun initial => P initial ** OF? ** SF? ** ZF? ** CF? ** PF?)
                                               (fun initial x b => P initial ** AL ~= x ** OF? ** SF? ** CF? ** PF?)
                                               accumulate
                                               (fun x => x == value)).
  { repeat match goal with
             | [ H : is_true (only_last _ _ _) |- _ ] => idtac; rewrite only_last__only_last'/only_last' in H
             | [ H : is_true (_ && _) |- _ ] => apply andb_prop in H
             | [ H : _ = true |- _ ] => move/eqP in H
             | _ => progress destruct_head and
             | _ => by hyp_rewrite *
             | _ => done
           end. }
  { assumption. }
  { basic apply H_body; eassumption. }
  { basic apply *. rewrite  subB_eq0.
    repeat match goal with
             | _ => done
             | [ |- context[if ?x then _ else _] ] => case_eq x
             | _ => progress simpl
           end. }
Qed.


Example addB_until_zero_prog_safe ch o s z c p S al
: S |-- (Forall initial (x : BYTE) (xs : seq BYTE) (pf1 : only_last (fun t : BYTE => t == #0) x xs),
         (loopy_basic (AH ~= initial ** AL ~= al ** OSZCP o s z c p)
                      (accumulate_until_value_prog #0 (ADD AH, AL) ch)
                      (foldr catOP empOP (map (inOP (zeroExtend n8 ch)) (x::xs)))
                      ((AH ~= (foldl (fun x y => addB x y) initial (drop_last x xs)))
                         ** AL ~= (last x xs) ** OF? ** SF? ** ZF ~= true ** CF? ** PF?))).
Proof.
  specintros => *. 
  admit. (*basic apply (@accumulate_until_value_prog_safe #0 _ (fun x => AH ~= x)) => *. first assumption.
  basic apply *. *)
Qed.

Import Streams.

Definition stream_to_in_out (in_c out_c : BYTE) (ls : Stream BYTE) : OPred
  := map_opred_to_stream (In (zeroExtend n8 in_c)) (fun v => (Out (zeroExtend n8 out_c) v)::nil) ls.

Definition echo_once in_c out_c :=
  (IN in_c, AL;;
   OUT out_c, AL).

Definition echo_once_OP_spec (in_c out_c : BYTE) v := catOP (inOP (zeroExtend n8 in_c) v) (outOP (zeroExtend n8 out_c) v).

Example safe_echo_once al in_c out_c
: |-- Forall v, basic (AL ~= al)
                      (echo_once in_c out_c)
                      (echo_once_OP_spec in_c out_c v)
                      (AL ~= v).
Proof.
  specintros => v. rewrite /echo_once/echo_once_OP_spec.
  basic apply *.
  basic apply *.
Qed.

Instance: forall in_c out_c, instrrule (echo_once in_c out_c) := fun in_c out_c al => @safe_echo_once al in_c out_c.

Definition echo in_c out_c := while (TEST EAX, EAX) CC_O false (echo_once in_c out_c).

Lemma eq_opred_stream__echo_once in_c out_c s
: (catOP (echo_once_OP_spec in_c out_c (hd s)) (stream_to_in_out in_c out_c (tl s)))
    |-- (stream_to_in_out in_c out_c s).
Proof.
  rewrite /echo_once_OP_spec/stream_to_in_out.
  destruct s.
  rewrite !map_opred_to_stream_def //=.
  rewrite /inOP/outOP ?catOPA.
  do !(apply lorR2; f_cancel).
Qed.

Lemma echo_safe in_c out_c eax
: |-- (Forall (s : Stream BYTE),
       (loopy_basic (EAX ~= eax ** AL? ** OSZCP?)
                    (echo in_c out_c)
                    (stream_to_in_out in_c out_c s)
                    lfalse)).
Proof.
  rewrite /echo.
  eapply @while_rule_ind
  with (I_logic := fun _ b => false == b)
         (Otest := fun _ => empOP)
         (Obody := fun s => echo_once_OP_spec in_c out_c (hd s))
         (I_state := fun s _ => EAX ~= eax ** AL? ** SF? ** ZF? ** CF? ** PF?)
         (transition_body := @tl _)
         (O_after_test := fun s => default_PointedOPred
                                     (catOP (echo_once_OP_spec in_c out_c (hd s)) (stream_to_in_out in_c out_c (tl s))));
    do ![ progress rewrite -> ?empOPL, -> ?eq_opred_stream__echo_once
        | specintros => *
        | done
        | by ssimpl
        | basic apply *
        | progress simpl OPred_pred
        | progress move => *
        | progress rewrite /stateIsAny
        | reflexivity ].
Qed.
