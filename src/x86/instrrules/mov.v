(** * MOV instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [unhideReg] *).

(** ** Generic rule *)
Lemma MOV_rule d ds oldv:
  |-- specAtDstSrc ds (fun V v =>
      basic (V oldv) (MOVOP d ds) empOP (V v)).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall d ds, instrrule (MOVOP d ds) := @MOV_rule.

(** ** Register to register *)
Lemma MOV_RR_rule (r1 r2:GPReg32) v1 v2:
  |-- basic (r1 ~= v1 ** r2 ~= v2) (MOV r1, r2) empOP (r1 ~= v2 ** r2 ~= v2).
Proof. basic apply *. Qed.

Lemma MOV_RanyR_rule (r1 r2:GPReg32) v2:
  |-- basic (r1? ** r2 ~= v2) (MOV r1, r2) empOP (r1 ~= v2 ** r2 ~= v2).
Proof. unhideReg r1 => old. basic apply *. Qed.

(** ** Immediate to register *)
Lemma MOV_RI_rule (r:GPReg32) (v1 v2:DWORD) :
  |-- basic (r ~= v1) (MOV r, v2) empOP (r ~= v2).
Proof. basic apply *. Qed.

Lemma MOV_RanyI_rule (r:GPReg32) (v2:DWORD) :
  |-- basic r? (MOV r, v2) empOP (r ~= v2).
Proof. unhideReg r => old. basic apply *. Qed.

(** ** Memory to register *)
(*
Lemma MOV_RM_rule (pd:DWORD) (r1 r2:GPReg32) offset (v1 v2: DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2)
            (MOV r1, [r2 + offset]) empOP
            (r1 ~= v2 ** r2 ~= pd ** pd +# offset :-> v2).
Proof. basic apply *. Qed.

Lemma MOV_RanyM_rule (pd:DWORD) (r1 r2:GPReg32) offset (v2: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd +# offset :-> v2)
            (MOV r1, [r2 + offset]) empOP
            (r1 ~= v2 ** r2 ~= pd ** pd +# offset :-> v2).
Proof. unhideReg r1 => old. basic apply *. Qed.
*)

Lemma MOV_RanyInd_rule (pd:DWORD) (r1:GPReg32) (v2: DWORD) :
  |-- basic (r1? ** ADRtoADDR (a:=AdSize4) pd :-> v2)
            (MOV r1, [pd]) empOP
            (r1 ~= v2 ** ADRtoADDR (a:=AdSize4) pd :-> v2).
Proof. unhideReg r1 => old. basic apply *. Qed.

Lemma MOV_RM0_rule (pd:ADDR32) (r1 r2:GPReg32) (v1 v2: DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd :-> v2)
            (MOV r1, [r2]) empOP
            (r1 ~= v2 ** r2 ~= pd ** pd :-> v2).
Proof. attempt basic apply *. rewrite /eval.computeAdr/eval.computeDisplacement. rewrite ->bitsopsprops.addB0. 
by  ssimpl. 
rewrite /eval.computeAdr/eval.computeDisplacement. rewrite ->bitsopsprops.addB0. 
by ssimpl. Qed.

Lemma MOV_RanyM0_rule (pd:ADDR32) (r1 r2:GPReg32) (v2: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd :-> v2)
            (MOV r1, [r2]) empOP
            (r1 ~= v2 ** r2 ~= pd ** pd :-> v2).
Proof. unhideReg r1 => old. basic apply MOV_RM0_rule. Qed.

(** ** Register to memory *)
(*
Lemma MOV_MR_rule (p: ADDR32) (r1 r2: GPReg32) offset (v1 v2:DWORD) :
  |-- basic (r1~=p ** p +# offset :-> v1 ** r2~=v2)
            (MOV [r1 + offset], r2) empOP
            (r1~=p ** p +# offset :-> v2 ** r2~=v2).
Proof. basic apply *. Qed.

(** ** Immediate to memory *)
Lemma MOV_MI_rule s (pd:DWORD) (r:GPReg32) offset (v:VWORD s) (w:IMM s) :
  |-- basic (r ~= pd ** pd +# offset :-> v)
            (MOVOP _ (DstSrcMI _ (mkMemSpec (Some(r, None)) #offset) w)) empOP
            (r ~= pd ** pd +# offset :-> eval.getImm w).
Proof. basic apply *. Qed.
*)

Lemma MOV_M0R_rule (pd:ADDR32) (r1 r2:GPReg32) (v1 v2: DWORD) :
  |-- basic (r1 ~= pd ** pd :-> v1 ** r2 ~= v2)
            (MOV [r1], r2) empOP
            (r1 ~= pd ** pd :-> v2 ** r2 ~= v2).
Proof. attempt basic apply *. 
rewrite /eval.computeAdr/eval.computeDisplacement. rewrite ->bitsopsprops.addB0. 
by  ssimpl. 
rewrite /eval.computeAdr/eval.computeDisplacement. rewrite ->bitsopsprops.addB0. 
by ssimpl. Qed.

Lemma MOV_IndR_rule (pd:DWORD) (r:GPReg32) (v1 v2: DWORD) :
  |-- basic (ADRtoADDR (a:=AdSize4) pd :-> v1 ** r ~= v2)
            (MOV [pd], r) empOP
            (ADRtoADDR (a:=AdSize4) pd :-> v2 ** r ~= v2).
Proof. basic apply *. Qed.

(*
Lemma MOV_MbR_rule (p: DWORD) (r1:GPReg32) (r2: Reg8) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** r2 ~= v2)
            (MOV [r1 + offset], r2) empOP
            (r1 ~= p ** p +# offset :-> v2 ** r2 ~= v2).
Proof. basic apply *. Qed.

Lemma MOV_RMb_rule (p: DWORD) (r1:GPReg32) (r2:Reg8) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** r2 ~= v2)
            (MOV r2, [r1 + offset]) empOP
            (r1 ~= p ** p +# offset :-> v1 ** r2 ~= v1).
Proof. basic apply *. Qed.

Lemma MOV_MbI_rule (pd:DWORD) (r1:GPReg32) offset (v1 v2:BYTE) :
  |-- basic (r1 ~= pd ** pd +# offset :-> v1)
            (MOV BYTE [r1 + offset], v2) empOP
            (r1 ~= pd ** pd +# offset :-> v2).
Proof. basic apply *. Qed.
*)