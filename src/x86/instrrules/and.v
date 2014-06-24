(** * AND instruction *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

(** ** Generic AND *)
Lemma AND_rule (ds:DstSrc true) (v1: DWORD) :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP true OP_AND ds)
             (let v := andB v1 v2 in
              D v ** OSZCP false (msb v) (v == #0) false (lsb v))).
Proof. do_instrrule_triple. Qed.

(** We open a section in order to localize the hints *)
Section InstrRules.

Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : basicapply.
Hint Rewrite
  addB0 low_catB : basicapply.

Hint Unfold OSZCP stateIsAny : spred.

(** ** AND r1, r2 *)
Corollary AND_RR_rule (r1 r2:Reg) v1 (v2:DWORD) :
  |-- basic (r1~=v1 ** r2 ~= v2 ** OSZCP?)
            (AND r1, r2)
            (let v := andB v1 v2 in r1~=v ** r2 ~= v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. basicapply (AND_rule (DstSrcRR true r1 r2)). Qed.

(** ** AND r1, [r2 + offset] *)
Corollary AND_RM_rule (pbase:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) :
  |-- basic (r1~=v1 ** OSZCP?)
            (AND r1, [r2 + offset])
            (let v:= andB v1 v2 in r1~=v ** OSZCP false (msb v) (v == #0) false (lsb v))
      @ (r2 ~= pbase ** pbase +# offset :-> v2).
Proof. autorewrite with push_at. basicapply (AND_rule (DstSrcRM true r1 (mkMemSpec (Some(r2, None)) #offset))). Qed.

Corollary AND_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (AND r1, [r2 + offset]) (r1~=andB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. basicapply (AND_RM_rule (pbase:=pd) (r1:=r1) (r2:=r2) (v1:=v1) (v2:=v2) (offset:=offset)). Qed.

(** ** AND r, v *)
Lemma AND_RI_rule (r:Reg) v1 (v2:DWORD) :
  |-- basic (r~=v1 ** OSZCP?)
            (AND r, v2)
            (let v:= andB v1 v2 in r~=v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. basicapply (AND_rule (DstSrcRI true r v2)). Qed.
End InstrRules.
