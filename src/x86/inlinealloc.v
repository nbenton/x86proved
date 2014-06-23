Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic program macros.
Require Import instr instrsyntax instrcodec instrrules reader pointsto cursor.

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
Definition allocInv (infoBlock: DWORD) :=
  Exists base: DWORD,
  Exists count: DWORD,
  infoBlock :-> base **
  infoBlock +#4 :-> count **
  memAny base count.

(* Allocate memory.
     infoBlock: Src  is pointer to two-word heap information block
     n: nat representing number of bytes to be allocated
     failed: DWORD is label to branch to on failure
   If successful, EDI contains pointer to byte just beyond allocated block.
*)
Definition allocImp infoBlock (n: nat) (failed: DWORD) : program :=
  MOV ESI, infoBlock;;
  MOV EDI, [ESI:Reg];;
  ADD EDI, n;;
  JC  failed;;  (* A carry indicates unsigned overflow *)
  CMP [ESI+4], EDI;;
  JC  failed;;  (* A carry indicates unsigned underflow *)
  MOV [ESI], EDI.

Definition allocSpec n (fail:DWORD) inv code :=
  Forall i j : DWORD, (
      safe @ (EIP ~= fail ** EDI?) //\\
      safe @ (EIP ~= j ** Exists p, EDI ~= p +# n ** memAny p (p +# n))
    -->>
      safe @ (EIP ~= i ** EDI?)
    )
    @ (ESI? ** OSZCP? ** inv)
    <@ (i -- j :-> code).

Hint Unfold allocSpec : specapply.

(* Perhaps put a |> on the failLabel case *)

Require Import tuple.
Corollary ADD_RI_ruleAux (r:Reg) v1 (v2:DWORD):
  |-- basic (r~=v1 ** OSZCP?) (ADD r, v2)
            (let v := addB v1 v2 in
             r~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) (fst (adcB false v1 v2)) (lsb v)).
Proof. generalize (@ADD_RI_rule r v1 v2). by elim (adcB false v1 _). Qed.

Lemma inlineAlloc_correct n failed infoBlock : |-- allocSpec n failed (allocInv infoBlock) (allocImp infoBlock n failed).
Proof.
  rewrite /allocSpec/allocImp.
  specintros => *. unfold_program. specintros => *.

  (* MOV ESI, infoBlock *)
  specapply MOV_RanyI_rule; first by ssimpl.

  (* MOV EDI, [ESI] *)
  rewrite {2}/allocInv. specintros => base limit.
  specapply MOV_RanyM0_rule; first by ssimpl.

  (* ADD EDI, bytes *)
  specapply ADD_RI_ruleAux; first by ssimpl.

  (* JC failed *)
  specapply JC_rule; first by rewrite /OSZCP; ssimpl.
  repeat specsplit.
  { rewrite <-spec_reads_frame. rewrite <-spec_later_weaken.
    autorewrite with push_at. apply limplValid. apply landL1. cancel1.
    rewrite /stateIsAny /allocInv. by sbazooka. }

  (* CMP [ESI+4], EDI *)
  specintro. move/eqP => Hcarry.
  specapply CMP_MR_ZC_rule; first by rewrite /stateIsAny; sbazooka.

  (* JC failed *)
  specapply JC_rule; first by ssimpl.

  repeat specsplit.
  { rewrite <-spec_reads_frame. rewrite <-spec_later_weaken.
    autorewrite with push_at. apply limplValid. apply landL1. cancel1.
    rewrite /stateIsAny/allocInv. sbazooka. }

  (* MOV [ESI], EDI *)
  specintro => LT.
  specapply MOV_M0R_rule; first by ssimpl.
  { rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
    apply: landL2. cancel1.
    rewrite /allocInv. ssplits.
    rewrite /stateIsAny/natAsDWORD. sbazooka.
    apply memAnySplit.
    { apply: addB_leB.
      apply injective_projections; [ by rewrite Hcarry
                                   | by generalize @adcB ]. }
    { simpl. rewrite ltBNle eqb_negLR /negb /natAsDWORD in LT. by rewrite (eqP LT). } }
Qed.
