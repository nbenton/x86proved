Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program spectac.
Require Import instr instrsyntax instrcodec instrrules reader pointsto cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Lemma basic_local S P c Q:
  (forall l, S |-- basic P (c l) Q) ->
  S |-- basic P (prog_declabel c) Q.
Proof.
  move=> H. rewrite /basic. rewrite /memIs /=. specintros => i j l.
  specialize (H l). lforwardR H.
  - apply lforallL with i. apply lforallL with j. reflexivity.
  apply H.
Qed.

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
  |-- (
      |> safe @ (b == cv /\\ EIP ~= a ** ConditionIs cc b) //\\
         safe @ (b == (~~cv) /\\ EIP ~= q ** ConditionIs cc b) -->>
      safe @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCC cc cv a).
Proof.
rewrite /JCC/relToAbs.
unfold_program. specintros => i1 i2 H1 H2.
rewrite -H2. rewrite H1. specapply JCCrel_rule. by ssimpl.
rewrite addB_subBK.
rewrite <-spec_reads_frame. apply: limplAdj.
apply: landL2. autorewrite with push_at.
specsplit.
- apply: landL1. cancel1. cancel1. sbazooka.
- apply: landL2. cancel1. sbazooka.
Qed.

Lemma JZ_rule a (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (b == true  /\\ EIP ~= a ** ZF ~= b) //\\
         safe @ (b == false /\\ EIP ~= q ** ZF ~= b) -->>
      safe @ (EIP ~= p ** ZF ~= b)
    ) <@ (p -- q :-> JZ a).
Proof.
  replace (ZF ~= b) with (ConditionIs CC_Z b) by reflexivity.
  apply: JCC_rule.
Qed.

Lemma JC_rule a (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (b == true  /\\ EIP ~= a ** CF ~= b) //\\
         safe @ (b == false /\\ EIP ~= q ** CF ~= b) -->>
      safe @ (EIP ~= p ** CF ~= b)
    ) <@ (p -- q :-> JC a).
Proof.
  replace (CF ~= b) with (ConditionIs CC_B b) by reflexivity.
  apply: JCC_rule.
Qed.

Lemma JMP_I_rule (a: DWORD) (p q: DWORD) :
  |-- (|> safe @ (EIP ~= a) -->> safe @ (EIP ~= p)) <@
        (p -- q :-> JMP a).
Proof.
rewrite /JMP/relToAbs.
unfold_program. specintros => i1 i2 H1 H2.
rewrite -H2 H1. specapply JMPrel_I_rule. by ssimpl.
rewrite addB_subBK. rewrite <-spec_reads_frame.
apply: limplAdj. apply: landL2. autorewrite with push_at.
cancel1. cancel1. sbazooka.
Qed.


Lemma JMP_R_rule (r:Reg) addr (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addr ** r ~= addr) -->> safe @ (EIP ~= p ** r ~= addr)) <@
        (p -- q :-> JMP (JmpTgtR r)).
Proof.
  rewrite /JMP. apply JMPrel_R_rule.
Qed.

Lemma CALL_I_rule (a:DWORD) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, (
      |> safe @ (EIP ~= a ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALL a).
Proof.
specintros => w sp.
rewrite /CALL/relToAbs.
unfold_program. specintros => i1 i2 H1 H2.
rewrite -H2 H1. specapply CALLrel_I_rule. by ssimpl.
rewrite addB_subBK. rewrite <-spec_reads_frame.
autorewrite with push_at.
apply: limplAdj. apply: landL2. cancel1. cancel1.
sbazooka.
Qed.

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

  Lemma if_rule cond (value:bool) pthen pelse P Q S:
    S |-- basic (P value ** ConditionIs cond value) pthen Q ->
    S |-- basic (P (~~value) ** ConditionIs cond (~~value)) pelse Q ->
    S |-- basic (Exists b, P b ** ConditionIs cond b)
                (ifthenelse cond value pthen pelse)
                Q.
  Proof.
    move=> Hthen Helse. apply basic_local => THEN. apply basic_local => END.
    rewrite /basic. specintros => i j b.
    unfold_program.
    specintros => i1 i2 i3 i4 <- -> i5 -> ->.

    (* JCC cond value THEN *)
    specapply JCC_rule. by ssimpl.

    specsplit.
    - (* THEN branch *)
      rewrite <-spec_later_weaken. specintro. move/eqP => ->.
      specapply Hthen. by ssimpl.
       rewrite <-spec_reads_frame. apply: limplAdj. autorewrite with push_at.
       apply: landL2. cancel1. by ssimpl.

    (* ELSE branch *)
    specintro. move/eqP => ->.
    specapply Helse. by ssimpl.

    (* JMP END *)
    specapply JMP_I_rule. by ssimpl.
    rewrite <-spec_later_weaken.
    rewrite <-spec_reads_frame. apply: limplAdj. autorewrite with push_at.
    apply: landL2. by (cancel1; reflexivity).
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

  Lemma while_rule ptest cond (value:bool) pbody (I:bool->_) P S:
    S |-- basic P ptest (Exists b, I b ** ConditionIs cond b) ->
    S |-- basic (I value ** ConditionIs cond value) pbody P ->
    S |-- basic P (while ptest cond value pbody)
                (I (~~value) ** ConditionIs cond (~~value)).
  Proof.
    move=> Htest Hbody. apply basic_local => BODY. apply basic_local => test.
    rewrite /basic. specintros => i j. unfold_program.
    specintros => _ _ <- ->  _ _ <- -> i1. rewrite !empSPL.

    (* We need to set up Lob induction but not for this instruction. This is a
       bit awkward. *)
    assert (|> safe @ (EIP ~= test ** P) -->>
        safe @ (EIP~=i ** P) //\\ safe @ (EIP ~= test ** P) |--
            safe @ (EIP~=i ** P)) as Hlob.
    - etransitivity; [|by apply landL1].
      instantiate (1 := safe @ (EIP ~= test ** P)).
      apply spec_lob_context. autorewrite with push_later.
      autorewrite with push_at. apply: limplL; first exact: landL2.
      exact: landL1. apply _.
    rewrite <-Hlob => {Hlob}.

    specsplit.
    (* JMP TEST *)
    - specapply JMP_I_rule. by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. apply: landL2. by (autorewrite with push_at; reflexivity).

    (* ptest *)
    specapply Htest. by ssimpl.

    (* JCC cond value BODY *)
    specintro => b.
    specapply JCC_rule. by ssimpl.

    (* Now there are two cases. Either we jumped to the loop body, or we fell
       through and exited the loop. *)
    specsplit.
    - autorewrite with push_at. rewrite ->landL2; last reflexivity.
      rewrite <-spec_later_impl, <-spec_later_weaken.
      (* pbody *)
      specapply Hbody.
      - sdestruct. move/eqP => ->. by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. autorewrite with push_at. cancel1. by ssimpl.

    (* End of loop *)
    rewrite <-spec_reads_frame. apply: limplAdj.
    apply: landL2. apply: landL1. autorewrite with push_at.
    cancel1. sdestruct. move/eqP => ->. by ssimpl.
  Qed.

  (* Special case if the test is read-only *)
  Lemma while_rule_ro ptest cond (value:bool) pbody (I:bool->_) S:
    let P := (Exists b, I b) ** (Exists b, ConditionIs cond b) in
    S |-- basic P ptest (Exists b, I b ** ConditionIs cond b) ->
    S |-- basic (I value ** ConditionIs cond value) pbody P ->
    S |-- basic P (while ptest cond value pbody)
                (I (~~value) ** ConditionIs cond (~~value)).
  Proof. apply while_rule. Qed.

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
    S |-- basic P ptest (Exists b, I b ** ConditionIs cond b) ->
    (forall SKIP, S |-- basic (I value ** ConditionIs cond value) (pbody SKIP) P) ->
    S |-- basic (I (~~value) ** ConditionIs cond (~~value)) pcoda Q ->
    S |-- basic P (whileWithExit ptest cond value pbody pcoda) Q.
  Proof.
    move=> Htest Hbody Hcoda. apply basic_local => BODY. apply basic_local => test.
    apply basic_local => SKIP.
    rewrite /basic. specintros => i j. unfold_program.
    specintros => _ _ <- ->  _ _ <- -> i1 i2 i3 -> ->. rewrite !empSPL.

    (* We need to set up Lob induction but not for this instruction. This is a
       bit awkward. *)
    assert (|> safe @ (EIP ~= test ** P) -->>
        safe @ (EIP~=i ** P) //\\ safe @ (EIP ~= test ** P) |--
            safe @ (EIP~=i ** P)) as Hlob.
    - etransitivity; [|by apply landL1].
      instantiate (1 := safe @ (EIP ~= test ** P)).
      apply spec_lob_context. autorewrite with push_later.
      autorewrite with push_at. apply: limplL; first exact: landL2.
      exact: landL1. apply _.
    rewrite <-Hlob => {Hlob}.

    specsplit.
    (* JMP TEST *)
    - specapply JMP_I_rule. by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. apply: landL2. by (autorewrite with push_at; reflexivity).

    (* ptest *)
    specapply Htest. by ssimpl.

    (* JCC cond value BODY *)
    specintro => b.
    specapply JCC_rule. by ssimpl.

    (* Now there are two cases. Either we jumped to the loop body, or we fell
       through and exited the loop. *)
    specsplit.
    - autorewrite with push_at. rewrite ->landL2; last reflexivity.
      rewrite <-spec_later_impl, <-spec_later_weaken.
      (* pbody *)
      specapply (Hbody SKIP).
      - sdestruct. move/eqP => ->. by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. autorewrite with push_at. cancel1. by ssimpl.

    (* End of loop *)
    specapply Hcoda. sdestructs => EQ. rewrite (eqP EQ). sbazooka.
    rewrite <-spec_reads_frame. apply: limplAdj.
    apply: landL2. apply: landL1. autorewrite with push_at.
    cancel1. by ssimpl.
  Qed.



End While.

