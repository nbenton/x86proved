Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.finfun Ssreflect.tuple Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.charge.ilogic.
Require Import x86proved.x86.program x86proved.x86.programassem x86proved.x86.programassemcorrect x86proved.x86.imp x86proved.x86.call.
Require Import x86proved.reader x86proved.spred x86proved.septac x86proved.pointsto x86proved.spec x86proved.spectac x86proved.x86.basic x86proved.x86.reg.
Require Import x86proved.cursor x86proved.safe x86proved.x86.instrrules x86proved.chargetac.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.macros Coq.Strings.Ascii x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.x86.screenspec x86proved.x86.screenimp.

Open Scope instr_scope.
Local Transparent ILFun_Ops.

Definition codeAddr:DWORD := #x"00300000".

Definition Cgcd :=
  Cseq (Cassign xa (eliteral #100)) (
  Cseq (Cassign xb (eliteral #60)) ( (* their GCD is 20, which is octal 024 *)
  Cwhile (esubtract xa xb) (
    Cif (elessthan xa xb) (
      Cassign xb (esubtract xb xa)
    ) (
      Cassign xa (esubtract xa xb)
    )
  )
  )).

(* TODO: stronger spec *)
Lemma Cgcd_correct:
  |-- triple ltrue Cgcd ltrue.
Proof.
  eapply triple_seq.
  - eapply triple_roc; [|done|apply triple_assign].
    apply subst_true_special_case.
  eapply triple_seq.
  - eapply triple_roc; [|done|apply triple_assign].
    apply subst_true_special_case.
  eapply triple_roc; last apply triple_while.
  - reflexivity.
  - done.
  eapply triple_roc; last apply triple_if.
  - reflexivity.
  - reflexivity.
  - eapply triple_roc; last apply triple_assign; last reflexivity.
    by rewrite -> asn_subst_ltrue; apply ltrueR.
  - eapply triple_roc; last apply triple_assign; last reflexivity.
    by rewrite -> asn_subst_ltrue; apply ltrueR.
Qed.

Definition gcd_program : program := compile_cmd Cgcd.

Definition gcd_bytes := assemble codeAddr gcd_program.

Definition screenAddr: DWORD := screenBase +# numCols*2*34.
Definition rightpos: DWORD := screenAddr +# (2*(11-1)).
Definition showOctal_program : program :=
    (* A 32-bit octal number can take up 11 digits. Each digit is two bytes. *)
      (* Print EAX in octal, stepping on EBX AND EDX *)
      MOV EBX, rightpos;;
      MOV ECX, 3;;
      while (TEST EAX, EAX) CC_Z false ( (* while EAX <> 0 *)
        MOV EDX, 7;; (* bit mask *)
        AND EDX, EAX;;
        ADD EDX, nat_of_ascii "0";;
        MOV [EBX], DL;; (* write to screen *)
        SHR EAX, 3;; (* shift right *)
        SUB EBX, 2(* move one character left on the screen *)
      ).

(* This is the theorem that is true for code under @ *)
Theorem gcd_safe: forall endAddr: DWORD,
  |-- (safe @ (EIP ~= endAddr ** codeAddr -- endAddr :-> compile_cmd Cgcd) -->> 
       safe @ (EIP ~= codeAddr ** codeAddr -- endAddr :-> gcd_bytes))
        @ (EAX? ** EBX? ** ECX? ** EDX? ** OSZCP?).
Proof.
  move=> endAddr. rewrite /gcd_bytes. 
  autorewrite with push_at.
  rewrite -> assemble_correct; last first. by vm_compute.
  rewrite /gcd_program. 
  have H := Cgcd_correct. rewrite /triple in H. autorewrite with push_at in H.
  superspecapply H. 
  - rewrite /asn_denot /stack_denot. rewrite /stateIsAny.
    sdestructs => a b c.
    pose s x := match x with | xa => a | xb => b | xc => c end.
    ssplit. instantiate (2:=s). ssplit; first done. rewrite /s. by ssimpl.

  rewrite /asn_denot /stack_denot /stateIsAny. 
  finish_logic_with sbazooka.   
Qed.


(*
(* This is not true if we replace <@ with @ because the code might update gcd_bytes but leave their decoding the same *)
Theorem gcd_safe: forall endAddr: DWORD,
  |-- (safe @ (EIP ~= endAddr) -->> safe @ (EIP ~= codeAddr))
        @ (EAX? ** EBX? ** ECX? ** EDX? ** OSZCP?)
        c@ (codeAddr -- endAddr :-> gcd_bytes).
Proof.
  move=> endAddr. rewrite /gcd_bytes. 
  autorewrite with push_at.
  rewrite ->assemble_correct; last first. by vm_compute.
  rewrite /gcd_program.
  have H := Cgcd_correct. rewrite /triple in H. autorewrite with push_at in H.
  superspecapply H.
  - rewrite /asn_denot/stack_denot. rewrite /stateIsAny.
    sdestructs => a b c.
    pose s x := match x with | xa => a | xb => b | xc => c end.
    ssplit. instantiate (2:=s). ssplit; first done. rewrite /s. by ssimpl.
  rewrite /asn_denot /stack_denot /stateIsAny. 
  finish_logic_with sbazooka. 
Qed.

*)

(* This is the plain version of the theorem, not obscured by fancy spec logic
   constructs. *)
(*
Corollary gcd_safe_nonfancy: forall (endAddr: DWORD) k R,
  safe k (EIP ~= endAddr ** EAX? ** EBX? ** ECX? ** EDX? ** OSZCP? **
          codeAddr -- endAddr :-> gcd_bytes ** R) ->
  safe k (EIP ~= codeAddr ** EAX? ** EBX? ** ECX? ** EDX? ** OSZCP? **
          codeAddr -- endAddr :-> gcd_bytes ** R).
Proof.
  move=> endAddr k R.
  pose proof (gcd_safe endAddr). rewrite ->spec_reads_entails_at in H; [|apply _].
  autorewrite with push_at in H.
  apply landAdj in H. lforwardL H.
  - apply landR; [apply ltrueR|done].
  specialize (H k R). unfold "|--" in H.
Qed.
*)

Definition gcdEx : option (seq BYTE) :=
  assemble codeAddr (
  gcd_program;;
    clsProg;;
    showOctal_program;;
(*
    oneStepScreen;;
    MOV ECX, 10;; MOV EDX, 10;;
    makeGlider;;
        delay;;
    MOV ECX, 20;; MOV EDX, 20;;
    makeGlider;;
        delay;;
        oneStepScreen;;
*)
    LOCAL busy;
(*      busy:;;*)
        JMP busy
  ).
