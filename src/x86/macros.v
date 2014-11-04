Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.obs x86proved.x86.basic x86proved.x86.program x86proved.spectac.
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
  |-- ((|> safe @ (b == cv /\\ EIP ~= a ** ConditionIs cc b)) //\\
         safe @ (b == (~~cv) /\\ EIP ~= q ** ConditionIs cc b) -->>
      safe @ (EIP ~= p ** ConditionIs cc b))
    @ (p -- q :-> JCC cc cv a).
Proof.
rewrite /JCC/relToAbs.
unfold_program. specintros => i1 i2 H1 H2. subst. 
rewrite -H2. 
supersafeapply JCCrel_rule. 
case E: (b == cv).
+ rewrite addB_subBK. finish_logic_with sbazooka. 
+ replace (b == ~~cv) with true by (destruct b; by destruct cv).  
  autorewrite with push_at. apply limplValid. apply landL2. rewrite <-spec_later_weaken. 
  finish_logic_with sbazooka. 
Qed.

Global Instance: forall a cc cv, instrrule (JCC cc cv a) := @JCC_rule.

Lemma JZ_rule a (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (b == true  /\\ EIP ~= a ** ZF ~= b) //\\
         safe @ (b == false /\\ EIP ~= q ** ZF ~= b) -->>
      safe @ (EIP ~= p ** ZF ~= b)
    ) @ (p -- q :-> JZ a).
Proof.
  change (ZF ~= b) with (ConditionIs CC_Z b).
  apply: JCC_rule.
Qed.

Lemma JC_rule a (b:bool) (p q: DWORD) :
  |-- (|> safe @ (b == true  /\\ EIP ~= a ** CF ~= b) //\\
         safe @ (b == false /\\ EIP ~= q ** CF ~= b) -->>
      safe @ (EIP ~= p ** CF ~= b)
    ) @ (p -- q :-> JC a).
Proof.
  change (CF ~= b) with (ConditionIs CC_B b).
  apply: JCC_rule.
Qed.

Lemma JMP_I_rule (a: DWORD) (p q: DWORD) :
  |-- (|> safe @ (EIP ~= a) -->> safe @ (EIP ~= p)) @
        (p -- q :-> JMP a).
Proof.
rewrite /JMP/relToAbs.
unfold_program. specintros => i1 i2 -> <-. 
supersafeapply JMPrel_I_rule. 
rewrite addB_subBK. 
finish_logic_with sbazooka. 
Qed.

Global Instance: forall (a : DWORD), instrrule (JMP a) := @JMP_I_rule.

Lemma JMP_R_rule (r:Reg) addr (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addr ** r ~= addr) -->> safe @ (EIP ~= p ** r ~= addr)) @
        (p -- q :-> JMP (JmpTgtR r)).
Proof. apply JMPrel_R_rule. Qed.

Global Instance: forall (a : Reg), instrrule (JMP (JmpTgtR a)) := @JMP_R_rule.

Lemma CALL_I_rule (a:DWORD) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, (
      |> safe @ (EIP ~= a ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** ESP~=sp    ** sp-#4 :-> w)
    ) @ (p -- q :-> CALL a).
Proof.
specintros => w sp.
rewrite /CALL/relToAbs.
unfold_program. specintros => i1 i2 -> <-.
supersafeapply CALLrel_I_rule.
rewrite addB_subBK. finish_logic_with sbazooka. 
Qed.

Global Instance: forall (a : DWORD), instrrule (CALL a) := @CALL_I_rule.

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
      (rewrite /basic; specintros => *; unfold_program);
      (specintros => *; do! subst);
      (** Tell the instrrule machinery about the "then" and "else" cases. *)
      pose proof (Hthen : instrrule pthen);
      pose proof (Helse : instrrule pelse).

   Lemma if_rule cond (value:bool) pthen pelse P Q S:
    S |-- basic (P value ** ConditionIs cond value) pthen Q ->
    S |-- basic (P (~~value) ** ConditionIs cond (~~value)) pelse Q ->
    S |-- basic (Exists b, P b ** ConditionIs cond b)
                          (ifthenelse cond value pthen pelse) 
                          Q.
  Proof.
    pre_if pthen pelse.
    supersafeapply JCC_rule. 
    rewrite <- spec_later_weaken.
    specsplit; specintro => /eqP ->. rewrite empSPL. 
    rewrite spec_at_at. supersafeapply Hthen. 
    rewrite <- spec_frame. finish_logic_with ssimpl. 
    rewrite spec_at_at. supersafeapply Helse. 
    supersafeapply JMP_I_rule. 
    rewrite <- spec_later_weaken. finish_logic_with ssimpl. 
  Qed.

  Global Instance: forall cond value pthen pelse, instrrule (ifthenelse cond value pthen pelse) := @if_rule.

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
    - supersafeapply JMP_I_rule. by finish_logic.

    (* ptest *)
    supersafeapply Htest. 

    (* JCC cond value BODY *)
    specintro => b.
    supersafeapply JCC_rule.  

    (* Now there are two cases. Either we jumped to the loop body, or we fell
       through and exited the loop. *)
    specsplit.
    - autorewrite with push_at. rewrite <-spec_later_impl, <-spec_later_weaken. 
      specintros => /eqP ->. supersafeapply Hbody.  
      finish_logic_with sbazooka. 

    (* End of loop *)
    specintros => /eqP ->.
    finish_logic_with sbazooka.  
  Qed.
  
  (* Special case if the test is read-only *)
  Lemma while_rule_ro ptest cond (value:bool) pbody (I:bool->_) S:
    let P := (Exists b, I b) ** (Exists b, ConditionIs cond b) in
    S |-- basic P ptest (Exists b, I b ** ConditionIs cond b) ->
    S |-- basic (I value ** ConditionIs cond value) pbody P ->
    S |-- basic P (while ptest cond value pbody)
                (I (~~value) ** ConditionIs cond (~~value)).
  Proof. apply while_rule. Qed.
End While.