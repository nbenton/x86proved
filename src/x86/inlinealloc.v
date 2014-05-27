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
    @ (ESI? ** OSZCP_Any ** inv)
    <@ (i -- j :-> code).

Hint Unfold allocSpec : specapply.

(* Perhaps put a |> on the failLabel case *)

Hint Unfold 
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst mkRegMemR
  DWORDorBYTEregIs
  : basicapply.
Hint Rewrite
  addB0 : basicapply.

Require Import tuple.
Lemma CMP_MR_ZC_rule (pd: DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OSZCP_Any) (CMP [r1+offset], r2)
            (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OF? ** SF? ** PF? ** 
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. unfold makeBOP.
eapply basic_basic.
have R:= (@CMP_ruleZC true (DstSrcMR true (mkMemSpec (Some (r1, None)) #offset) r2) v1).
rewrite /specAtDstSrc/specAtMemSpecDst/DWORDorBYTEregIs in R. 
apply (lforallE_spec v2) in R.
autorewrite with push_at in R. 
apply (lforallE_spec pd) in R. 
autorewrite with push_at in R. 
apply R. 
sbazooka. 
sbazooka. 
Qed. 

Lemma inlineAlloc_correct n failed infoBlock : |-- allocSpec n failed (allocInv infoBlock) (allocImp infoBlock n failed).  
Proof.  
  rewrite /allocSpec/allocImp. specintros => i j. unfold_program. 
  specintros => i1 i2 i3 i4 i5 i6.

  (* MOV ESI, infoBlock *)  
  specapply MOV_RanyI_rule; first by ssimpl. 

  (* MOV EDI, [ESI] *)
  rewrite {2}/allocInv. specintros => base limit.
  specapply MOV_RanyM0_rule; first by ssimpl.

  (* ADD EDI, bytes *)
  elim E:(adcB false base (fromNat n)) => [carry res].
  rewrite /ConstImm. specapply ADD_RI_rule; first by ssimpl. 

  (* JC failed *)
  rewrite E. specapply JC_rule.
  rewrite /OSZCP. sbazooka. 

  specsplit.
    rewrite <-spec_reads_frame. rewrite <-spec_later_weaken.
    autorewrite with push_at. apply limplValid. apply landL1. cancel1.
    rewrite /OSZCP_Any/stateIsAny /allocInv. by sbazooka.

  (* CMP [ESI+4], EDI *)
  specintro. move/eqP => Hcarry. subst carry.
  specapply CMP_MR_ZC_rule. rewrite /OSZCP_Any/stateIsAny. sbazooka.  

  (* JC failed *)
  specapply JC_rule; first by ssimpl.

  specsplit.
  - rewrite <-spec_reads_frame. rewrite <-spec_later_weaken.
    autorewrite with push_at. apply limplValid. apply landL1. cancel1.
    rewrite /OSZCP_Any/stateIsAny/allocInv. sbazooka.
 
  (* MOV [ESI], EDI *)
  specintro. rewrite {1}ltBNle {1}eqb_negLR /negb. move => Hcarry0. 
  specapply (MOV_M0R_rule (pd:=infoBlock) (r1:=ESI)).
  - sbazooka. 
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  apply: landL2. cancel1.
  rewrite /OSZCP_Any/allocInv. ssplits.

  ssimpl. 
  have Hres: base +# n = res by rewrite /addB /dropmsb E.
  have Hless1 := addB_leB E.
  rewrite <-Hres in *.
  ssimpl. have MAS:= @memAnySplit base (base +# n) limit Hless1. 
  rewrite /leCursor in MAS. rewrite (eqP Hcarry0) in MAS. ssimpl.
  rewrite /stateIsAny. sbazooka. apply MAS => //.  
Qed.