(** * MOV instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [unhideReg] *).

(** ** Generic rule *)
Lemma MOV_rule d ds oldv:
  |-- specAtDstSrc ds (fun V v =>
      basic (V oldv) (MOVOP d ds) (V v)).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall d ds, instrrule (MOVOP d ds) := @MOV_rule.


(** ** Register to register *)
Lemma MOV_RR_rule (r1 r2:Reg) v1 v2:
  |-- basic (r1 ~= v1 ** r2 ~= v2) (MOV r1, r2) (r1 ~= v2 ** r2 ~= v2).
Proof. basic apply *. Qed.

Lemma MOV_RanyR_rule (r1 r2:Reg) v2:
  |-- basic (r1? ** r2 ~= v2) (MOV r1, r2) (r1 ~= v2 ** r2 ~= v2).
Proof. unhideReg r1 => old. basic apply *. Qed.

(** ** Immediate to register *)
Lemma MOV_RI_rule (r:Reg) (v1 v2:DWORD) :
  |-- basic (r ~= v1) (MOV r, v2) (r ~= v2).
Proof. basic apply *. Qed.

Lemma MOV_RanyI_rule (r:Reg) (v2:DWORD) :
  |-- basic r? (MOV r, v2) (r ~= v2).
Proof. unhideReg r => old. basic apply *. Qed.

(** ** Memory to register *)
Lemma MOV_RM_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2: DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2)
            (MOV r1, [r2 + offset]) 
            (r1 ~= v2 ** r2 ~= pd ** pd +# offset :-> v2).
Proof. basic apply *. Qed.

Lemma MOV_RanyM_rule (pd:DWORD) (r1 r2:Reg) offset (v2: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd +# offset :-> v2)
            (MOV r1, [r2 + offset]) 
            (r1 ~= v2 ** r2 ~= pd ** pd +# offset :-> v2).
Proof. unhideReg r1 => old. basic apply *. Qed.

Lemma MOV_RanyInd_rule (pd:DWORD) (r1:Reg) (v2: DWORD) :
  |-- basic (r1? ** pd :-> v2)
            (MOV r1, [pd]) 
            (r1 ~= v2 ** pd :-> v2).
Proof. unhideReg r1 => old. basic apply *. Qed.

Lemma MOV_RM0_rule (pd:DWORD) (r1 r2:Reg) (v1 v2: DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd :-> v2)
            (MOV r1, [r2]) 
            (r1 ~= v2 ** r2 ~= pd ** pd :-> v2).
Proof. basic apply *. Qed.

Lemma MOV_RanyM0_rule (pd:DWORD) (r1 r2:Reg) (v2: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd :-> v2)
            (MOV r1, [r2]) 
            (r1 ~= v2 ** r2 ~= pd ** pd :-> v2).
Proof. unhideReg r1 => old. basic apply *. Qed.

(** ** Register to memory *)
Lemma MOV_MR_rule (p: DWORD) (r1 r2: Reg) offset (v1 v2:DWORD) :
  |-- basic (r1~=p ** p +# offset :-> v1 ** r2~=v2)
            (MOV [r1 + offset], r2) 
            (r1~=p ** p +# offset :-> v2 ** r2~=v2).
Proof. basic apply *. Qed.

(** ** Immediate to memory *)
Lemma MOV_MI_rule s (pd:DWORD) (r:Reg) offset (v w:VWORD s) :
  |-- basic (r ~= pd ** pd +# offset :-> v)
            (MOVOP _ (DstSrcMI _ (mkMemSpec (Some(r, None)) #offset) w)) 
            (r ~= pd ** pd +# offset :-> w).
Proof. basic apply *. Qed.

Lemma MOV_M0R_rule (pd:DWORD) (r1 r2:Reg) (v1 v2: DWORD) :
  |-- basic (r1 ~= pd ** pd :-> v1 ** r2 ~= v2)
            (MOV [r1], r2) 
            (r1 ~= pd ** pd :-> v2 ** r2 ~= v2).
Proof. basic apply *. Qed.

Lemma MOV_IndR_rule (pd:DWORD) (r:Reg) (v1 v2: DWORD) :
  |-- basic (pd :-> v1 ** r ~= v2)
            (MOV [pd], r) 
            (pd :-> v2 ** r ~= v2).
Proof. basic apply *. Qed.


Lemma MOV_MbR_rule (p: DWORD) (r1:Reg) (r2: BYTEReg) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** r2 ~= v2)
            (MOV [r1 + offset], r2) 
            (r1 ~= p ** p +# offset :-> v2 ** r2 ~= v2).
Proof. basic apply *. Qed.

Lemma MOV_RMb_rule (p: DWORD) (r1:Reg) (r2:BYTEReg) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** r2 ~= v2)
            (MOV r2, [r1 + offset]) 
            (r1 ~= p ** p +# offset :-> v1 ** r2 ~= v1).
Proof. basic apply *. Qed.

Lemma MOV_MbI_rule (pd:DWORD) (r1:Reg) offset (v1 v2:BYTE) :
  |-- basic (r1 ~= pd ** pd +# offset :-> v1)
            (MOV BYTE [r1 + offset], v2) 
            (r1 ~= pd ** pd +# offset :-> v2).
Proof. basic apply *. Qed.
