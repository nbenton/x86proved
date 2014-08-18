Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.opred x86proved.septac x86proved.spec x86proved.obs x86proved.x86.basic x86proved.x86.program x86proved.spectac.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor.
Require Import x86proved.x86.basicprog (* for [instrrule] *).
Require Import x86proved.basicspectac x86proved.common_tactics x86proved.common_definitions x86proved.chargetac.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(* We define absolute jumps, calls and branches using labels *)
Definition relToAbs (c : DWORD -> Instr) : DWORD -> program :=
  fun a => LOCAL Next; c (subB a Next);; Next:;.

Definition JMP t := if t is JmpTgtI (mkTgt t) then relToAbs JMPrel t else JMPrel t.
Definition CALL t := if t is JmpTgtI (mkTgt t) then relToAbs CALLrel t else CALLrel t.
Definition JCC cc cv := relToAbs (JCCrel cc cv).

Arguments CALL (t)%ms.
Arguments JMP (t)%ms.

(*---------------------------------------------------------------------------
    Branch instructions
  ---------------------------------------------------------------------------*)
Notation "'JA'"  := (JCC CC_BE false) : instr_scope.
Notation "'JAE'" := (JCC CC_B  false) : instr_scope.
Notation "'JAB'" := (JCC CC_B  true)  : instr_scope.
Notation "'JBE'" := (JCC CC_BE true)  : instr_scope.
Notation "'JC'"  := (JCC CC_B  true)  : instr_scope.
Notation "'JE'"  := (JCC CC_Z true)   : instr_scope.
Notation "'JG'"  := (JCC CC_LE false) : instr_scope.
Notation "'JGE'" := (JCC CC_L false)  : instr_scope.
Notation "'JL'"  := (JCC CC_L true)   : instr_scope.
Notation "'JLE'" := (JCC CC_LE true)  : instr_scope.
Notation "'JNA'" := (JCC CC_BE true)  : instr_scope.
Notation "'JNB'" := (JCC CC_B false)  : instr_scope.
Notation "'JNBE'":= (JCC CC_BE false) : instr_scope.
Notation "'JNC'" := (JCC CC_B false)  : instr_scope.
Notation "'JNE'" := (JCC CC_Z false)  : instr_scope.
Notation "'JNG'" := (JCC CC_LE true)  : instr_scope.
Notation "'JNGE'":= (JCC CC_L true)   : instr_scope.
Notation "'JNL'" := (JCC CC_L false)  : instr_scope.
Notation "'JNLE'":= (JCC CC_LE false) : instr_scope.
Notation "'JNO'" := (JCC CC_O false)  : instr_scope.
Notation "'JNP'" := (JCC CC_P false)  : instr_scope.
Notation "'JNS'" := (JCC CC_S false)  : instr_scope.
Notation "'JNZ'" := (JCC CC_Z false)  : instr_scope.
Notation "'JO'"  := (JCC CC_O true)   : instr_scope.
Notation "'JP'"  := (JCC CC_P true)   : instr_scope.
Notation "'JPE'" := (JCC CC_P true)   : instr_scope.
Notation "'JPO'" := (JCC CC_P false)  : instr_scope.
Notation "'JS'"  := (JCC CC_S true)   : instr_scope.
Notation "'JZ'"  := (JCC CC_Z true)   : instr_scope.

Lemma JCC_rule a cc cv (b:bool) (p q: DWORD) :
  |-- Forall O, (
      obs O @ (EIP ~= (if b == cv then a else q) ** ConditionIs cc b) -->>
      obs O @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCC cc cv a).
Proof.
rewrite /JCC/relToAbs.
unfold_program. specintros => O i1 i2 H1 H2.
rewrite -H2. rewrite H1. specapply JCCrel_rule. by ssimpl.
rewrite addB_subBK.
rewrite <-spec_reads_frame. apply: limplAdj.
apply: landL2. autorewrite with push_at.
case E:(b == cv);
  by cancel1; sbazooka.
Qed.

Lemma JCC_loopy_rule a cc cv (b:bool) (p q: DWORD) :
  |-- Forall (O : PointedOPred), (
      |> obs O @ (b == cv /\\ EIP ~= a ** ConditionIs cc b) //\\
         obs O @ (b == (~~cv) /\\ EIP ~= q ** ConditionIs cc b) -->>
      obs O @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCC cc cv a).
Proof.
rewrite /JCC/relToAbs.
unfold_program. specintros => O i1 i2 H1 H2.
rewrite -H2. rewrite H1. specapply JCCrel_loopy_rule. by ssimpl.
rewrite addB_subBK.
rewrite <-spec_reads_frame. apply: limplAdj.
apply: landL2. autorewrite with push_at.
specsplit.
- apply: landL1. cancel1. cancel1. sbazooka.
- apply: landL2. cancel1. sbazooka.
Qed.

Global Instance: forall a cc cv, instrrule (JCC cc cv a) := @JCC_rule.
Global Instance: forall a cc cv, loopy_instrrule (JCC cc cv a) := @JCC_loopy_rule.

Lemma JZ_rule a (b:bool) (p q: DWORD) :
  |-- Forall O, (
      obs O @ (EIP ~= (if b then a else q) ** ZF ~= b) -->>
      obs O @ (EIP ~= p ** ZF ~= b)
    ) <@ (p -- q :-> JZ a).
Proof.
  change (ZF ~= b) with (ConditionIs CC_Z b).
  replace (if b then a else q) with (if b == true then a else q) by by case b.
  apply: JCC_rule.
Qed.

Lemma JZ_loopy_rule a (b:bool) (p q: DWORD) :
  |-- Forall (O : PointedOPred), (
      |> obs O @ (b == true  /\\ EIP ~= a ** ZF ~= b) //\\
         obs O @ (b == false /\\ EIP ~= q ** ZF ~= b) -->>
      obs O @ (EIP ~= p ** ZF ~= b)
    ) <@ (p -- q :-> JZ a).
Proof.
  change (ZF ~= b) with (ConditionIs CC_Z b).
  apply: JCC_loopy_rule.
Qed.

Lemma JC_rule a (b:bool) (p q: DWORD) :
  |-- Forall O, (
      obs O @ (EIP ~= (if b then a else q) ** CF ~= b) -->>
      obs O @ (EIP ~= p ** CF ~= b)
    ) <@ (p -- q :-> JC a).
Proof.
  change (CF ~= b) with (ConditionIs CC_B b).
  replace (if b then a else q) with (if b == true then a else q) by by case b.
  apply: JCC_rule.
Qed.

Lemma JC_loopy_rule a (b:bool) (p q: DWORD) :
  |-- Forall (O : PointedOPred), (
      |> obs O @ (b == true  /\\ EIP ~= a ** CF ~= b) //\\
         obs O @ (b == false /\\ EIP ~= q ** CF ~= b) -->>
      obs O @ (EIP ~= p ** CF ~= b)
    ) <@ (p -- q :-> JC a).
Proof.
  change (CF ~= b) with (ConditionIs CC_B b).
  apply: JCC_loopy_rule.
Qed.

Lemma JMP_I_rule (a: DWORD) (p q: DWORD) :
  |-- Forall O, (obs O @ (EIP ~= a) -->> obs O @ (EIP ~= p)) <@
        (p -- q :-> JMP a).
Proof.
rewrite /JMP/relToAbs.
unfold_program. specintros => O i1 i2 H1 H2.
rewrite -H2 H1. specapply JMPrel_I_rule. by ssimpl.
rewrite addB_subBK. rewrite <-spec_reads_frame.
apply: limplAdj. apply: landL2. autorewrite with push_at.
cancel1. sbazooka.
Qed.

Lemma JMP_I_loopy_rule (a: DWORD) (p q: DWORD) :
  |-- Forall (O : PointedOPred), (|> obs O @ (EIP ~= a) -->> obs O @ (EIP ~= p)) <@
        (p -- q :-> JMP a).
Proof.
rewrite /JMP/relToAbs.
unfold_program. specintros => O i1 i2 H1 H2.
rewrite -H2 H1. specapply JMPrel_I_loopy_rule. by ssimpl.
rewrite addB_subBK. rewrite <-spec_reads_frame.
apply: limplAdj. apply: landL2. autorewrite with push_at.
cancel1. cancel1. sbazooka.
Qed.

Global Instance: forall (a : DWORD), instrrule (JMP a) := @JMP_I_rule.
Global Instance: forall (a : DWORD), loopy_instrrule (JMP a) := @JMP_I_loopy_rule.

Lemma JMP_R_rule (r:Reg) addr (p q: DWORD) :
  |-- Forall O, (obs O @ (EIP ~= addr ** r ~= addr) -->> obs O @ (EIP ~= p ** r ~= addr)) <@
        (p -- q :-> JMP (JmpTgtR r)).
Proof.
  rewrite /JMP. apply JMPrel_R_rule.
Qed.

Lemma JMP_R_loopy_rule (r:Reg) addr (p q: DWORD) :
  |-- Forall (O : PointedOPred), (|> obs O @ (EIP ~= addr ** r ~= addr) -->> obs O @ (EIP ~= p ** r ~= addr)) <@
        (p -- q :-> JMP (JmpTgtR r)).
Proof.
  rewrite /JMP. apply JMPrel_R_loopy_rule.
Qed.

Global Instance: forall (a : Reg), instrrule (JMP (JmpTgtR a)) := @JMP_R_rule.
Global Instance: forall (a : Reg), loopy_instrrule (JMP (JmpTgtR a)) := @JMP_R_loopy_rule.

Lemma CALL_I_rule (a:DWORD) (p q: DWORD) :
  |-- Forall O, Forall w: DWORD, Forall sp:DWORD, (
         obs O @ (EIP ~= a ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALL a).
Proof.
specintros => O w sp.
rewrite /CALL/relToAbs.
unfold_program. specintros => i1 i2 H1 H2.
rewrite -H2 H1. specapply CALLrel_I_rule. by ssimpl.
rewrite addB_subBK. rewrite <-spec_reads_frame.
autorewrite with push_at.
apply: limplAdj. apply: landL2. cancel1.
sbazooka.
Qed.

Lemma CALL_I_loopy_rule (a:DWORD) (p q: DWORD) :
  |-- Forall (O : PointedOPred), Forall w: DWORD, Forall sp:DWORD, (
      |> obs O @ (EIP ~= a ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         obs O @ (EIP ~= p  ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALL a).
Proof.
specintros => O w sp.
rewrite /CALL/relToAbs.
unfold_program. specintros => i1 i2 H1 H2.
rewrite -H2 H1. specapply CALLrel_I_loopy_rule. by ssimpl.
rewrite addB_subBK. rewrite <-spec_reads_frame.
autorewrite with push_at.
apply: limplAdj. apply: landL2. cancel1. cancel1.
sbazooka.
Qed.

Global Instance: forall (a : DWORD), instrrule (CALL a) := @CALL_I_rule.
Global Instance: forall (a : DWORD), loopy_instrrule (CALL a) := @CALL_I_loopy_rule.

Section If.
(*=ifthenelse *)
Definition ifthenelse (cond: Condition) (value: bool)
  (pthen pelse: program) : program :=
  LOCAL THEN; LOCAL END;
    JCC cond value THEN;;
      pelse;; JMP END;;
    THEN:;; pthen;;
    END:;.
(*=End *)

  Local Ltac pre_if pthen pelse :=
    let Hthen := fresh "Hthen" in
    let Helse := fresh "Helse" in
    intros Hthen Helse;
      (try specintros => *; idtac);
      (** handle the locals *)
      rewrite /ifthenelse;
      do 2(basic apply * => *; idtac);
      (rewrite /parameterized_basic; specintros => *; unfold_program);
      (specintros => *; do! subst);
      (** Tell the instrrule machinery about the "then" and "else" cases. *)
      pose proof (Hthen : instrrule pthen);
      pose proof (Helse : instrrule pelse).

  Lemma if_rule cond (value:bool) pthen pelse P O Q S:
    S |-- basic (P value ** ConditionIs cond value) pthen (O value) (Q value) ->
    S |-- basic (P (~~value) ** ConditionIs cond (~~value)) pelse (O (~~value)) (Q (~~value)) ->
    S |-- Forall b, basic (P b ** ConditionIs cond b)
                          (ifthenelse cond value pthen pelse) (O b)
                          (Q b).
  Proof.
    pre_if pthen pelse.
    do ![ specapply *; first by ssimpl
        | split_eip_match
        | finish_logic ].
  Qed.

  Lemma if_loopy_rule cond (value:bool) pthen pelse P (O : bool -> PointedOPred) Q S:
    S |-- loopy_basic (P value ** ConditionIs cond value) pthen (O value) (Q value) ->
    S |-- loopy_basic (P (~~value) ** ConditionIs cond (~~value)) pelse (O (~~value)) (Q (~~value)) ->
    S |-- Forall b, loopy_basic (P b ** ConditionIs cond b)
                                (ifthenelse cond value pthen pelse) (O b)
                                (Q b).
  Proof.
    pre_if pthen pelse.
    do ![ specapply *; first by ssimpl
        | split_eip_match
        | finish_logic ].
  Qed.

  Global Instance: forall cond value pthen pelse, instrrule (ifthenelse cond value pthen pelse) := @if_rule.
  Global Instance: forall cond value pthen pelse, loopy_instrrule (ifthenelse cond value pthen pelse) := @if_loopy_rule.

  Lemma if_rule_const_io cond (value:bool) pthen pelse P O Q S:
    S |-- basic (P value ** ConditionIs cond value) pthen O Q ->
    S |-- basic (P (~~value) ** ConditionIs cond (~~value)) pelse O Q ->
    S |-- basic (Exists b, P b ** ConditionIs cond b)
                (ifthenelse cond value pthen pelse) O
                Q.
  Proof.
    move => Hthen Helse. specintro => ?.
Ltac appears_in subterm superterm :=
  idtac;
  match superterm with
    | appcontext[subterm] => idtac
    | _ => fail 1 "Term" subterm "does not appear in term" superterm
  end.
Hint Extern 0 (syntax_unify (opts := {| infer_constant_functions := true |}) (?f ?x) ?b)
=> is_evar f; atomic x; not is_evar x; not appears_in x b;
   let T := type_of x in
   unify f (fun _ : T => b);
     cbv beta;
     exact (Coq.Init.Logic.eq_refl b) : typeclass_instances.
    basic apply *; cbv beta; assumption.
  Qed.

  Lemma if_loopy_rule_const_io cond (value:bool) pthen pelse P (O : PointedOPred) Q S:
    S |-- loopy_basic (P value ** ConditionIs cond value) pthen O Q ->
    S |-- loopy_basic (P (~~value) ** ConditionIs cond (~~value)) pelse O Q ->
    S |-- loopy_basic (Exists b, P b ** ConditionIs cond b)
                (ifthenelse cond value pthen pelse) O
                Q.
  Proof.
    move => Hthen Helse. specintro => ?.
    basic apply loopy *; cbv beta; assumption.
  Qed.

End If.

Section While.
  (* A macro for a structured "while" loop with parameters:
     - ptest: code that performs the loop test
     - cond: the Condition to test the flags for when deciding whether to loop
     - value: whether the test is inverted (usually false)
     - pbody: the loop body
   *)
(*=while *)
Definition while (ptest: program)
  (cond: Condition) (value: bool)
  (pbody: program) : program :=
  LOCAL BODY; LOCAL test;
    JMP test;;
  BODY:;; pbody;;
  test:;;
    ptest;;
    JCC cond value BODY.
(*=End *)


  Section helper.
    (** We need these opaque to speed up setoid rewriting. *)
    Local Opaque lforall limpl illater spec_at spec_reads.
    Lemma safe_while_later_helper_faster
          {S T S1 c1 S2 c2 R}
          (H0 : S |-- ((Forall (x : T), ((((*|>*)S1) @ c1 -->> (|>S2 x) @ c2 x)))
                       -->>
                       (Forall (x : T), ((S1 @ c1 -->> S2 x @ c2 x)))) <@ R)
    : S |-- |>(Forall (x : T), ((S1 @ c1 -->> S2 x @ c2 x) <@ R))
          -->>
          (Forall (x : T), ((S1 @ c1 -->> S2 x @ c2 x) <@ R)).
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

    Lemma safe_while_later_helper_drop_later
          {S A T X1 X2 X3 X4 R}
          (H0 : S |-- (A //\\ (Forall (x : T), ((*|>*)X1 x) @ (X2 x)) -->> ((*|>*)X3) @ X4) <@ R)
    : S |-- (A //\\ (Forall (x : T), (|>X1 x) @ (X2 x)) -->> (|>X3) @ X4) <@ R.
    Proof.
      rewrite -> H0; clear H0.
      do ![ f_cancel; [] ].
      repeat match goal with
               | [ |- context[Forall _ : _, |>_] ] => setoid_rewrite <- spec_later_forall
               | [ |- context[(|>_) @ _] ]         => setoid_rewrite -> spec_at_later
               | [ |- context[(|>_) -->> (|>_)] ]  => setoid_rewrite <- spec_later_impl
               | [ |- ?A //\\ _ -->> _ |-- ?A //\\ _ -->> _ ] => apply strip_andL_impl
               | [ |- ?A |-- |>?A ] => apply spec_later_weaken
             end.
    Qed.

  End helper.

  (** general while rule *)
  (** Make all dependent arguments implicit so we can pass them by name *)
  Lemma while_rule_pre_ind {quantT}
        {ptest} {cond : Condition} {value : bool} {pbody}
        {S}
        {transition_body : quantT -> quantT}
        {P : quantT -> SPred} {Otest : quantT -> OPred} {Obody : quantT -> OPred} {O : quantT -> PointedOPred}
        {O_after_test : quantT -> PointedOPred}
        {I_state : quantT -> bool -> SPred}
        {I_logic : quantT -> bool -> Prop}
        {Q : SPred}
        (Htest : S |-- (Forall (x : quantT),
                        (loopy_basic (P x)
                                     ptest
                                     (Otest x)
                                     (Exists b, I_logic x b /\\ I_state x b ** ConditionIs cond b))))
        (Hbody : S |-- (Forall (x : quantT),
                        (loopy_basic (I_logic x value /\\ I_state x value ** ConditionIs cond value)
                                     pbody
                                     (Obody x)
                                     (P (transition_body x)))))
        (H_after_test : forall x, catOP (Otest x) (O_after_test x) |-- O x)
        (H_body_after_test : forall x, I_logic x value -> catOP (Obody x) (O (transition_body x)) |-- O_after_test x)
        (H_empty : forall x, I_logic x (~~value) -> empOP |-- O_after_test x)
        (Q_correct : Exists x', I_logic x' (~~value) /\\ I_state x' (~~value) ** ConditionIs cond (~~value) |-- Q)
  : S |-- (Forall (x : quantT),
           loopy_basic (P x)
                       (while ptest cond value pbody)
                       (O x)
                       Q).
  Proof.
    rewrite /while.
    specintro => x.
    rewrite <- Q_correct.
    do 2 basic apply loopy * => ?.
    rewrite /parameterized_basic.
    do ?[ progress subst
        | progress specintros => *
        | progress unfold_program ].

    (** The jmp at the very beginning, to the test *)
    specapply *; first by ssimpl.

    lrevert x.
    apply spec_lob_context.
    apply landAdj.
    apply safe_while_later_helper_faster.
    do !setoid_rewrite lforall_limpl_commute.
    let H := match goal with |- _ |-- ((?A -->> ?B) -->> ?A -->> ?C) <@ _ => constr:(triple_limpl' A B C) end in
    setoid_rewrite <- H.
    specintros => x.

    (** Remember the instrrules so [specapply *] knows about them. *)
    instrrule remember Htest.
    instrrule remember Hbody.
    (** Pre-prove the side condition of the test [specapply *], so it's picked up automatically. *)
    assert (forall x O', catOP (Otest x) (catOP (O_after_test x) O') |-- catOP (O x) O')
      by by move => *; rewrite <- H_after_test, <- ?catOPA.
    assert (forall x O', I_logic x value -> catOP (Obody x) (catOP (O (transition_body x)) O') |-- catOP (O_after_test x) O')
      by by move => *; rewrite <- H_body_after_test, <- ?catOPA.

    (** the test *)
    specapply *; first by ssimpl.

    (** the conditional jump (jcc) *)
    specintros => *.
    loopy_specapply *; first by ssimpl.

    (** we split into the body case and the leaving case *)
    specsplit.

    { (** body case *)
      (** we need to drop the laters ([|>]), first *)
      set_evars; autorewrite with push_at push_later; subst_evars.
      specintros. move/eqP => *; subst.
      apply safe_while_later_helper_drop_later.
      simpl OPred_pred.

      specapply *; try (by ssimpl); try (by eauto); simpl OPred_pred.

      finish_logic_with ltac:(autorewrite with push_at; eauto; ssimpl). }

    { (** leaving case *)
      specintros. move/eqP => *; subst.
      simpl OPred_pred.
      rewrite <- H_empty, empOPL; try assumption.

      repeat match goal with
               | [ |- context[@lor ?Frm ?ILOps empOP ?Q] ] => rewrite <- (@lorR1 Frm ILOps _ empOP Q empOP (reflexivity _))
               | [ |- context[catOP empOP ?P] ] => rewrite -> (empOPL P)
               | _ => by finish_logic_with ltac:(autorewrite with push_at; eauto; sbazooka)
             end. }
  Qed.

  (** Now we talk about the while rule where the post condition is
      allowed to depend on what we're quantifying over, but only if it
      doesn't change when we transition. *)
  Lemma while_rule_ind {quantT}
        {ptest} {cond : Condition} {value : bool} {pbody}
        {S}
        {transition_body : quantT -> quantT}
        {P : quantT -> SPred} {Otest : quantT -> OPred} {Obody : quantT -> OPred} {O : quantT -> PointedOPred}
        {O_after_test : quantT -> PointedOPred}
        {I_state : quantT -> bool -> SPred}
        {I_logic : quantT -> bool -> bool}
        {Q : quantT -> SPred}
        (Htest : S |-- (Forall (x : quantT),
                        (loopy_basic (P x)
                                     ptest
                                     (Otest x)
                                     (Exists b, I_logic x b /\\ I_state x b ** ConditionIs cond b))))
        (Hbody : S |-- (Forall (x : quantT),
                        (loopy_basic (I_logic x value /\\ I_state x value ** ConditionIs cond value)
                                     pbody
                                     (Obody x)
                                     (P (transition_body x)))))
        (H_after_test : forall x, catOP (Otest x) (O_after_test x) |-- O x)
        (H_body_after_test : forall x, I_logic x value -> catOP (Obody x) (O (transition_body x)) |-- O_after_test x)
        (H_empty : forall x, I_logic x (~~value) -> empOP |-- O_after_test x)
        (Q_correct : forall x, I_logic x (~~value) /\\ I_state x (~~value) ** ConditionIs cond (~~value) |-- Q x)
        (Q_safe : forall x, I_logic x value -> Q (transition_body x) |-- Q x)
  : S |-- (Forall (x : quantT),
           loopy_basic (P x)
                       (while ptest cond value pbody)
                       (O x)
                       (Q x)).
  Proof.
    specintro => x0.
    pose (existT (fun x => Q x |-- Q x0) x0 (reflexivity _)) as xH.
    change x0 with (projT1 xH) at 1 2.
    clearbody xH.
    lrevert xH.
    eapply @while_rule_pre_ind
    with (P := fun xH => P (projT1 xH))
           (Otest := fun xH => Otest (projT1 xH))
           (Obody := fun xH => Obody (projT1 xH))
           (O := fun xH => O (projT1 xH))
           (O_after_test := fun xH => O_after_test (projT1 xH))
           (I_state := fun xH => I_state (projT1 xH))
           (I_logic := fun xH b => I_logic (projT1 xH) b /\ Q (projT1 xH) |-- Q x0)
           (transition_body := fun xH => existT _ (if I_logic (projT1 xH) value then transition_body (projT1 xH) else projT1 xH) _);
      simpl projT1; simpl projT2;
      (try specintros; move => *; destruct_head_hnf sigT; destruct_head and);
      eauto.
    { basic apply Htest. }
    { basic apply Hbody. by hyp_rewrite *. }
    { by hyp_rewrite *; auto. }
    { apply lexistsL => *; ssimpl; destruct_head_hnf sigT; destruct_head and.
      etransitivity; try eassumption.
      by rewrite <- Q_correct; ssimpl. }
    Grab Existential Variables.
    { destruct xH; simpl; etransitivity; [ | eassumption ].
      case E:(I_logic _ _); auto. }
  Qed.


  (** general while rule *)
  (** grumble, grumble, if we don't do this, rewriting doesn't pick things up right *)
  Local Opaque roll_starOP.
  Lemma while_rule
        ptest (cond : Condition) (value : bool) pbody
        (PP : nat -> SPred -> Prop) (Obody : nat -> OPred) (IP : nat -> (bool -> SPred) -> Prop) Q S
        (transition_test : forall P n, PP n P -> bool -> SPred)
        (transition_body : forall I n, IP n I -> SPred)
        (transition_test_correct : forall P n (H : PP n P), IP n (transition_test P n H))
        (transition_body_correct : forall I n (H : IP n I), PP (n.+1) (transition_body I n H))
        (Q_correct : forall n P (H : PP n P), transition_test P n H (~~value) |-- Q)
        (Htest : forall P n (H' : PP n P) (I := transition_test P n H'),
                   IP n I
                   -> S |-- loopy_basic P ptest empOP (Exists b, I b ** ConditionIs cond b))
        (Hbody : forall I n (H' : IP n I) (P := transition_body I n H'),
                   PP (n.+1) P
                   -> S |-- loopy_basic (I value ** ConditionIs cond value) pbody (Obody n) P)
        (P0 : SPred) (start : nat) (H0 : PP start P0)
  : S |-- (loopy_basic P0
                       (while ptest cond value pbody)
                       (roll_starOP Obody start)
                       (Q ** ConditionIs cond (~~value))).
  Proof.
    move start at bottom.
    move P0 at bottom.
    pose (existT (fun start => PP (fst start) (snd start)) (start, P0) H0) as x.
    change start with (fst (projT1 x)).
    change P0 with (snd (projT1 x)).
    clearbody x.
    clear P0 H0 start.
    lrevert x.
    eapply @while_rule_ind
    with (Otest := fun _ => empOP)
           (Obody := fun nPH => Obody (fst (projT1 nPH)))
           (I_logic := fun _ _ => true)
           (I_state := fun nPH => transition_test (snd (projT1 nPH)) (fst (projT1 nPH)) _)
           (transition_body := fun nPH => existT _ (_, transition_body _ _ _) _);
      repeat match goal with
               | _ => progress intros
               | _ => progress (simpl projT1; simpl projT2; simpl fst; simpl snd; simpl OPred_pred)
               | [ |- context[lpropand (is_true true) _] ] => setoid_rewrite -> lpropandtrue
               | [ |- _ |-- lforall _ ] => apply lforallR => ?
               | [ |- lexists _ |-- _ ] => apply lexistsL => ?
               | [ |- context[catOP _ (lexists _)] ] => rewrite -> catOP_lexists2
               | _ => by try ssimpl; eauto
               | [ |- _ |-- _ \\// _ ] => by apply lorR2; reflexivity
               | [ |- _ |-- _ \\// _ ] => by apply lorR1; reflexivity
               | [ |- _ |-- roll_starOP _ _ ] => etransitivity; last apply roll_starOP_def
             end.
    Grab Existential Variables.
    by simpl; eauto.
    by simpl; eauto.
    by apply projT2.
  Qed.

  (** I/O-free while rule *)
  Lemma while_rule_const_io ptest cond (value:bool) pbody (I:bool->_) P S:
    S |-- loopy_basic P ptest empOP (Exists b, I b ** ConditionIs cond b) ->
    S |-- loopy_basic (I value ** ConditionIs cond value) pbody empOP P ->
    S |-- loopy_basic P (while ptest cond value pbody) empOP
                (I (~~value) ** ConditionIs cond (~~value)).
  Proof.
    move => Htest Hbody.
    pose proof (fun Ht Hb =>
                  @while_rule ptest cond value pbody (fun _ => eq P) (fun _ => empOP) (fun _ I' => I = I') (I (~~value)) S
                              (fun _ _ _ => I) (fun _ _ _ => P)
                              (fun _ _ _ => reflexivity _) (fun _ _ _ => reflexivity _) (fun _ _ _ => reflexivity _)
                              Ht Hb
                              P 0) as H.
    cbv beta zeta in *.
    rewrite -> roll_starOP_empOP in H.
    by apply H => *; subst.
  Qed.

  (* Special case if the test is read-only *)
  Lemma while_rule_ro ptest cond (value:bool) pbody (I:bool->_) S:
    let P := (Exists b, I b) ** (Exists b, ConditionIs cond b) in
    S |-- loopy_basic P ptest empOP (Exists b, I b ** ConditionIs cond b) ->
    S |-- loopy_basic (I value ** ConditionIs cond value) pbody empOP P ->
    S |-- loopy_basic P (while ptest cond value pbody) empOP
                (I (~~value) ** ConditionIs cond (~~value)).
  Proof. apply while_rule_const_io. Qed.

  Definition whileWithExit (ptest: program)
      (cond: Condition) (value: bool)
      (pbody: DWORD -> program) (pcoda: program) : program :=
    LOCAL BODY;
    LOCAL test;
    LOCAL SKIP;
        JMP test;;
      BODY:;;
        pbody SKIP;;
      test:;;
        ptest;;
        JCC cond value BODY;;
        pcoda;;
      SKIP:;.

  Lemma whileWithExit_rule ptest cond (value:bool) pbody pcoda (I:bool->_) P Q S:
    S |-- loopy_basic P ptest empOP (Exists b, I b ** ConditionIs cond b) ->
    (forall SKIP, S |-- loopy_basic (I value ** ConditionIs cond value) (pbody SKIP) empOP P) ->
    S |-- loopy_basic (I (~~value) ** ConditionIs cond (~~value)) pcoda empOP Q ->
    S |-- loopy_basic P (whileWithExit ptest cond value pbody pcoda) empOP Q.
  Proof.
    move=> Htest Hbody Hcoda. apply basic_local => BODY. apply basic_local => test.
    apply basic_local => SKIP.
    rewrite /loopy_basic. specintros => i j O. unfold_program.
    specintros => _ _ <- ->  _ _ <- -> i1 i2 i3 -> ->. rewrite !empSPL.

    instrrule remember Htest.
    instrrule remember Hbody.
    instrrule remember Hcoda.

    (* We need to set up Lob induction but not for this instruction. This is a
       bit awkward. *)
    assert (|> obs O @ (EIP ~= test ** P) -->>
        obs O @ (EIP~=i ** P) //\\ obs O @ (EIP ~= test ** P) |--
            obs O @ (EIP~=i ** P)) as Hlob.
    - etransitivity; [|by apply landL1].
      instantiate (1 := obs O @ (EIP ~= test ** P)).
      apply spec_lob_context. autorewrite with push_later.
      autorewrite with push_at. apply: limplL; first exact: landL2.
      exact: landL1. apply _.
    rewrite -> empOPL. rewrite <-Hlob => {Hlob}.

    specsplit.
    (* JMP TEST *)
    - loopy_specapply *; first by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. apply: landL2. by (autorewrite with push_at; reflexivity).

    (* ptest *)
    specapply *; first by ssimpl.

    (* JCC cond value BODY *)
    specintro => b.
    loopy_specapply *; first by ssimpl.

    (* Now there are two cases. Either we jumped to the loop body, or we fell
       through and exited the loop. *)
    specsplit.
    - autorewrite with push_at. rewrite ->landL2; last reflexivity.
      rewrite <-spec_later_impl, <-spec_later_weaken.
      (* pbody *)
      specapply *.
      - sdestruct. move/eqP => ->. by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. autorewrite with push_at. cancel1. by ssimpl.

    (* End of loop *)
    specapply *.
    sdestructs => EQ. rewrite (eqP EQ). sbazooka.
    rewrite <-spec_reads_frame. apply: limplAdj.
    apply: landL2. apply: landL1. autorewrite with push_at.
    cancel1. by ssimpl.
  Qed.



End While.

Section Until.
  (** A macro for a structured "until" loop with parameters:
      - ptest: code that performs the loop test
      - cond: the Condition to test the flags for when deciding whether to loop
      - value: whether the test is inverted (usually false)
      - pbody: the loop body
   *)
  Definition until (ptest: program)
             (cond: Condition) (value: bool)
             (pbody: program) : program :=
    (pbody;;
     while ptest cond value pbody).

  (** general until rule *)
  Lemma until_rule
        ptest (cond : Condition) (value : bool) pbody
        (PP : nat -> SPred -> Prop) (Obody : nat -> OPred) (IP : nat -> (bool -> SPred) -> Prop) Q S
        (transition_test : forall P n, PP n P -> bool -> SPred)
        (transition_body : forall I n, IP n I -> SPred)
        (transition_test_correct : forall P n (H : PP n P), IP n (transition_test P n H))
        (transition_body_correct : forall I n (H : IP n I), PP (n.+1) (transition_body I n H))
        (Q_correct : forall n P (H : PP n P), transition_test P n H (~~value) |-- Q)
        (Htest : forall P n (H' : PP n P) (I := transition_test P n H'),
                   IP n I
                   -> S |-- loopy_basic P ptest empOP (Exists b, I b ** ConditionIs cond b))
        (Hbody : forall I n (H' : IP n I) (P := transition_body I n H'),
                   PP (n.+1) P
                   -> S |-- loopy_basic (I value ** ConditionIs cond value) pbody (Obody n) P)
        (P0 : bool -> SPred) (start : nat) (H0 : IP start P0)
        (Hbody_start : S |-- loopy_basic (P0 value) pbody (Obody start) (transition_body P0 start H0))
  : S |-- (loopy_basic (P0 value)
                       (until ptest cond value pbody)
                       (catOP (Obody start) (roll_starOP Obody (start.+1)))
                       (Q ** ConditionIs cond (~~value))).
  Proof.
    cbv zeta in *.
    rewrite /until.
    basic apply Hbody_start; clear Hbody_start.
    rewrite empSPR.
    eapply while_rule; try eassumption; instantiate; eauto.
  Qed.

  (** I/O-free while rule *)
  Lemma until_rule_const_io ptest cond (value:bool) pbody (I:bool->_) P P0 S:
    S |-- loopy_basic P0 pbody empOP P ->
    S |-- loopy_basic P ptest empOP (Exists b, I b ** ConditionIs cond b) ->
    S |-- loopy_basic (I value ** ConditionIs cond value) pbody empOP P ->
    S |-- loopy_basic P0 (until ptest cond value pbody) empOP
                (I (~~value) ** ConditionIs cond (~~value)).
  Proof.
    move => Hbody_start Htest Hbody.
    cbv zeta in *.
    rewrite /until.
    basic apply Hbody_start; clear Hbody_start.
    rewrite empSPR.
    eapply while_rule_const_io; assumption.
  Qed.

End Until.
