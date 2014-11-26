Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.opred x86proved.spec x86proved.spectac x86proved.obs x86proved.x86.basic x86proved.x86.program x86proved.x86.macros.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor.
Require Import x86proved.chargetac.

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
  ADD RDI, (BOPArgI OpSize8 (n:DWORD));;
  JC  failed;;  (* A carry indicates unsigned overflow *)
  CMP QWORD PTR [infoBlockReg + 8], RDI;;
  JC  failed;;  (* A carry indicates unsigned underflow *)
  MOV QWORD PTR [infoBlockReg], RDI.


Definition allocSpec n (failed:ADDR) inv code :=
  Forall i j : ADDR, Forall O : OPred, (
      obs O @ (UIP ~= failed ** RDI?) //\\
      obs O @ (UIP ~= j ** Exists p, RDI ~= p +# n ** memAny p (p +# n))
    -->>
      obs O @ (UIP ~= i ** RDI?)
    )
    @ (OSZCP? ** inv)
    <@ (i -- j :-> code).

Hint Unfold allocSpec : specapply.

(* Perhaps put a |> on the failLabel case *)

Lemma inlineAlloc_correct n failed : 
  |-- allocSpec n failed allocInv (allocImp n failed).
Proof.
  rewrite /allocSpec/allocImp.
  specintros => *. 
  unfold_program. specintros => *.
  autorewrite with push_at.

  (* MOV RDI, [infoBlockReg + 0] *)
  rewrite {3}/allocInv. specintros => infoBlock base limit. 
  rewrite {2}/(stateIsAny RDI). specintros => oldrdi.
Hint Rewrite -> signExtend_fromNat : ssimpl. 
Hint Rewrite -> addB0 : ssimpl. 

Hint Unfold fromSingletonMemSpec : specapply.
Require Import basicspectac.

  specapply *; first by sbazooka. 

  (* ADD RDI, n *)
  rewrite spec_at_at. rewrite spec_at_at. specapply *; first by sbazooka. 

  (* JC failed *)
  specapply JC_rule; first by rewrite /OSZCP; ssimpl.
  case Hcarry:(carry_addB base (signExtend _ (natAsDWORD n))). 
  { finish_logic. apply landL1. finish_logic. 
    rewrite /stateIsAny/allocInv. sbazooka.  }

 (* CMP [infoBlockReg + 8], RDI *)   
admit.
(*  specapply *. CMP_ruleZC. basicCMP_ZC. unfold UOPArgM4. specapply CMP_rule. 
  specapply CMP_IndR_ZC_rule; first by rewrite /stateIsAny; sbazooka.

  (* JC failed *)
  specapply JC_rule; first by ssimpl.

  case LT:(ltB _ _).
  { rewrite <-spec_reads_frame. apply limplValid. apply landL1. finish_logic. 
    rewrite /stateIsAny/allocInv. sbazooka. }

  (* MOV [infoBlock], EDI *)
  specapply MOV_IndR_rule; first by ssimpl.
  { rewrite <-spec_reads_frame. apply limplValid. apply landL2. finish_logic.
    rewrite /allocInv/stateIsAny/natAsDWORD. sbazooka.

    apply memAnySplit; last first.
    { simpl. rewrite ltBNle /natAsDWORD in LT. rewrite -> Bool.negb_false_iff in LT. admit. } 
    { apply: addB_leB. 
      apply injective_projections. Admitted. 
*)
Qed.