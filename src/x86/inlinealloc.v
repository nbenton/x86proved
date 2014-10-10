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
Definition allocInv (infoBlock: ADR AdSize4) :=
  Exists base: ADR AdSize4,
  Exists count: ADR AdSize4,
  ADRtoADDR infoBlock :-> base **
  ADRtoADDR (a:=AdSize4) (infoBlock +#4) :-> count **
  memAny (ADRtoADDR base) (ADRtoADDR count).

(* Allocate memory.
     infoBlock: Src  is pointer to two-word heap information block
     n: nat representing number of bytes to be allocated
     failed: DWORD is label to branch to on failure
   If successful, EDI contains pointer to byte just beyond allocated block.
*)
Definition allocImp (infoBlock:DWORD) (n: nat) (failed: ADDR) : program :=
  MOV EDI, [infoBlock];;
  ADD EDI, n;;
  JC  failed;;  (* A carry indicates unsigned overflow *)
  CMP [infoBlock+#4:DWORD], EDI;;
  JC  failed;;  (* A carry indicates unsigned underflow *)
  MOV [infoBlock], EDI.

Definition allocSpec n (fail:ADDR) inv code :=
  Forall i j : ADDR, Forall O : OPred, (
      obs O @ (UIP ~= fail ** EDI?) //\\
      obs O @ (UIP ~= j ** Exists p, EDI ~= p +# n ** memAny (ADRtoADDR (a:=AdSize4) p) (ADRtoADDR (a:=AdSize4) (p +# n)))
    -->>
      obs O @ (UIP ~= i ** EDI?)
    )
    @ (OSZCP? ** inv)
    <@ (i -- j :-> code).

Hint Unfold allocSpec : specapply.

(* Perhaps put a |> on the failLabel case *)

Lemma inlineAlloc_correct n failed infoBlock : |-- allocSpec n failed (allocInv infoBlock) (allocImp infoBlock n failed).
Proof.
  rewrite /allocSpec/allocImp.
  specintros => *. 
  unfold_program. specintros => *.
  autorewrite with push_at.

  (* MOV EDI, [infoBlock] *)
  rewrite {3}/allocInv. specintros => base limit. 
  (*rewrite {2}/(stateIsAny EDI). specintros => oldedi.*)
  specapply MOV_RanyInd_rule; first by ssimpl. 

  (* ADD EDI, bytes *)
  specapply ADD_RI_rule; first by ssimpl.

  (* JC failed *)
  specapply JC_rule; first by rewrite /OSZCP; ssimpl.
  case Hcarry:(carry_addB base (natAsDWORD n)). 
  { rewrite <-spec_reads_frame. apply limplValid. apply landL1. finish_logic. 
    rewrite /stateIsAny/allocInv. sbazooka.  }

  (* CMP [infoBlock+#4], EDI *)
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
