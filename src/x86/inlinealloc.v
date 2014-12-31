Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.spectac x86proved.x86.basic x86proved.x86.program x86proved.x86.macros.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor.
Require Import x86proved.chargetac x86proved.latertac.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.
(* Allocation invariant:
     infoBlock points to a pair of DWORDs:
       base, a pointer to the current available heap
       count, the number of bytes currently available
   Furthermore, "count" bytes of memory starting at "base" is defined
*)
Definition infoBlockReg := R14.
Definition allocInv :=
  Exists infoBlock: ADDR, 
  infoBlockReg ~= infoBlock **
  Exists base limit:ADDR,  
  infoBlock :-> base **
  infoBlock +#8 :-> limit **
  memAny base limit.

(* Allocate memory.
     infoBlock: Src  is pointer to two-word heap information block
     n: nat representing number of bytes to be allocated
     failed: ADDR is label to branch to on failure
   If successful, RDI contains pointer to byte just beyond allocated block.
*)
Definition allocImp (n: nat) (failed: ADDR) : program :=
  MOV RDI, QWORD PTR [infoBlockReg];;
  ADD RDI, (#n:IMM _);;
  JC  failed;;  (* A carry indicates unsigned overflow *)
  CMP QWORD PTR [infoBlockReg + 8], RDI;;
  JC  failed;;  (* A carry indicates unsigned underflow *)
  MOV QWORD PTR [infoBlockReg], RDI.

Definition allocSpec n (failed:ADDR) inv code :=
  Forall i j : ADDR, (
      safe @ (UIP ~= failed ** RDI?) //\\
      safe @ (UIP ~= j ** Exists p, RDI ~= p +# n ** memAny p (p +# n))
    -->>
      safe @ (UIP ~= i ** RDI?)
    )
    @ (OSZCP? ** inv)
    c@ (i -- j :-> code).

Hint Unfold allocSpec : specapply.
Require Import x86proved.basicspectac.

(* Perhaps put a |> on the failLabel case *)
Lemma inlineAlloc_correct n failed : 
  n < 2^n31 ->
  |-- allocSpec n failed allocInv (allocImp n failed).
Proof. 
  rewrite /allocSpec/allocImp. move => LT. 
  specintros => i j.   
  unfold_program. specintros => *. 
  (* Push invariant under implication so that we can instantiate existential pre and post *)
  rewrite spec_at_impl. rewrite /allocInv. specintros => infoBlock base limit. 
  rewrite {2}/(stateIsAny RDI). specintros => oldrdi. 
Hint Rewrite -> signExtend_fromNat : ssimpl. 
Hint Rewrite -> addB0 : ssimpl. 

Hint Unfold fromSingletonMemSpec : specapply.

Admitted.
(*
  (* MOV RDI, [infoBlockReg + 0] *)
  specapply *. ; first by sbazooka. 

  (* ADD RDI, n *)
  rewrite spec_at_at. rewrite spec_at_at. specapply *; first by sbazooka. 

  (* JC failed *)
  specapply JC_rule; first by rewrite /OSZCP; ssimpl.
  case Hcarry:(carry_addB base (signExtend _ (natAsDWORD n))). 
  { finish_logic. apply landL1. finish_logic. 
    rewrite /stateIsAny/allocInv. sbazooka.  }

 (* CMP [infoBlockReg + 8], RDI *)
  have RULE := (CMP_ruleZC (DstSrcMR _ _ (mkMemSpec _ None (Some (infoBlockReg:BaseReg _)) None 8) RDI)).
  specapply RULE. 
  rewrite /stateIsAny.
  sbazooka. (* Why doesn't this work? *)
  rewrite sepSPC. rewrite sepSPA. reflexivity. 
  clear RULE. 

  (* JC failed *)
  specapply JC_rule. rewrite /OSZCP. sbazooka. 

  case LT:(ltB _ _).
  { rewrite <-spec_reads_frame. apply limplValid. apply landL1. rewrite /allocInv. finish_logic_with sbazooka. 
    reflexivity. }

  (* MOV [infoBlock], RDI *)
  specapply *; first by ssimpl.
  { rewrite <-spec_reads_frame. apply limplValid. apply landL2. rewrite /eval.getImm. 
    rewrite -> (signExtend_fromNat _); last by done.
    rewrite /allocInv/stateIsAny/natAsDWORD/eval.computeEA/eval.computeDisplacement. finish_logic. ssimpl.
    (* sbazooka instantiates wrongly *)
    ssplits. instantiate (1:= limit).
    sbazooka. instantiate (1:= base). rewrite -> memAnySplit.
    ssimpl. reflexivity. 
    { apply: addB_leB. 
      apply injective_projections. rewrite -> signExtend_fromNat in Hcarry; last by done. apply Hcarry. 
      by simpl. } 
    { rewrite ltBNle /natAsDWORD in LT. simpl. rewrite -> Bool.negb_false_iff in LT. rewrite /eval.getImm in LT. 
      rewrite ->signExtend_fromNat in LT; last by done. apply LT. } }
Qed.
=======
  (* MOV EDI, [infoBlock] *)  
  superspecapply MOV_RanyInd_rule. 

  (* ADD EDI, bytes *)
  superspecapply *. 

  (* JC failed *)
  rewrite /OSZCP. 
  superspecapply JC_rule. 

  specsplit.
  simpllater. (*rewrite <- spec_frame. *) finish_logic_with sbazooka.

  (* CMP [infoBlock+#4], EDI *)
  specintro => /eqP => Hcarry. 

  specapply CMP_IndR_ZC_rule; rewrite /stateIsAny; sbazooka. 

  (* JC failed *)
  superspecapply JC_rule. 
  specsplit.
  - simpllater. (*rewrite <- spec_frame. *) finish_logic_with sbazooka.

  (* MOV [infoBlock], EDI *)
  superspecapply MOV_IndR_rule. 

  specintro => /eqP LT.

  { (*rewrite <- spec_frame. *) rewrite /stateIsAny/natAsDWORD. finish_logic. (*apply limplValid.
    autorewrite with push_at. *) apply landL2. finish_logic_with sbazooka.  

    apply memAnySplit.
    { apply: addB_leB.
      apply injective_projections; [ by rewrite Hcarry
                                   | by generalize @adcB ]. }
    { simpl. rewrite ltBNle /natAsDWORD in LT. rewrite -> Bool.negb_false_iff in LT. by rewrite LT. } }
Qed.
>>>>>>> master
*)