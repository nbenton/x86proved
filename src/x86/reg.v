(*===========================================================================
    Model for x86 registers
    Note that the EFL register (flags) is treated separately.

    These are registers as used inside instructions, and can refer to
    overlapping sections of the real machine state e.g. AL, AH, AX, EAX
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.choice Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.bitsrep.

(*---------------------------------------------------------------------------
    General purpose registers
  ---------------------------------------------------------------------------*)
(* General purpose registers, excluding RSP and RIP *)
(*=NonSPReg64 *)
Inductive NonSPReg64 := 
  RAX | RBX | RCX | RDX | RSI | RDI | RBP
| R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.
(*=End *)
Definition NonSPReg64_toNat r :=
  match r with RAX => 0 | RCX => 1 | RDX => 2 | RBX => 3 | RBP => 5 | RSI => 6 | RDI => 7 
             | R8 => 8 | R9 => 9 | R10 => 10 | R11 => 11 | R12 => 12 | R13 => 13 | R14 => 14 | R15 => 15 end.
Lemma NonSPReg64_toNat_inj : injective NonSPReg64_toNat. Proof. by repeat case => //. Qed.
Canonical Structure NonSPReg64_EqMixin := InjEqMixin NonSPReg64_toNat_inj.
Canonical Structure NonSPReg64_EqType := Eval hnf in EqType _ NonSPReg64_EqMixin.

(* General purpose registers: x86 has eight, x64 has sixteen *)
(*=GPReg64 *)
Inductive GPReg64 := mkGPReg64 (r: NonSPReg64) :> GPReg64 | RSP.
(*=End *)
Definition GPReg64_toNat r :=  match r with | RSP => 4 | mkGPReg64 r => NonSPReg64_toNat r end.
Lemma GPReg64_toNat_inj : injective GPReg64_toNat. Proof. by repeat case => //. Qed.
Canonical Structure GPReg64_EqMixin := InjEqMixin GPReg64_toNat_inj.
Canonical Structure GPReg64_EqType := Eval hnf in EqType _ GPReg64_EqMixin.

(*---------------------------------------------------------------------------
    Control registers
  ---------------------------------------------------------------------------*)
Inductive CReg := CR0 | CR1 | CR2 | CR3 | CR4.
Definition CRegToNat r :=  
  match r with CR0 => 0 | CR1 => 1 | CR2 => 2 | CR3 => 3 | CR4 => 4 end. 
Lemma CRegToNat_inj : injective CRegToNat. Proof. by repeat case => //. Qed.
Canonical Structure CRegEqMixin := InjEqMixin CRegToNat_inj.
Canonical Structure CRegEqType := Eval hnf in EqType _ CRegEqMixin.

(*---------------------------------------------------------------------------
    All registers
  ---------------------------------------------------------------------------*)
(* All registers, including RIP and control registers but still excluding the flags *)
(*=Reg64 *)
Inductive Reg64 := mkReg64 (r: GPReg64) :> Reg64 | mkCReg (r: CReg) | RIP.
(*=End *)
Definition Reg64_toNat r :=  
  match r with | RIP => 16 | mkReg64 r => GPReg64_toNat r | mkCReg r => 17+CRegToNat r end.
Lemma Reg64_toNat_inj : injective Reg64_toNat. Proof. by repeat case => //. Qed.
Canonical Structure Reg64_EqMixin := InjEqMixin Reg64_toNat_inj.
Canonical Structure Reg64_EqType := Eval hnf in EqType _ Reg64_EqMixin.

(* Addressable 32-bit slices of above *)
Inductive NonSPReg32 := mkNonSPReg32 (r: NonSPReg64).
Definition NonSPReg32_base r32 := let: mkNonSPReg32 r := r32 in r.
Lemma NonSPReg32_base_inj : injective NonSPReg32_base. Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure NonSPReg32_EqMixin := InjEqMixin NonSPReg32_base_inj.
Canonical Structure NonSPReg32_EqType := Eval hnf in EqType _ NonSPReg32_EqMixin.

Inductive GPReg32 := mkGPReg32 (r: GPReg64).
Definition GPReg32_base r32 := let: mkGPReg32 r := r32 in r.
Lemma GPReg32_base_inj : injective GPReg32_base. Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure GPReg32_EqMixin := InjEqMixin GPReg32_base_inj.
Canonical Structure GPReg32_EqType := Eval hnf in EqType _ GPReg32_EqMixin.

Inductive Reg32 := mkReg32 (r: Reg64).
Definition Reg32_base r32 := let: mkReg32 r := r32 in r.
Lemma Reg32_base_inj : injective Reg32_base. Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure Reg32_EqMixin := InjEqMixin Reg32_base_inj.
Canonical Structure Reg32_EqType := Eval hnf in EqType _ Reg32_EqMixin.

Coercion NonSPReg32_to_GPReg32 (r: NonSPReg32) := mkGPReg32 (NonSPReg32_base r).
Coercion GPReg32_to_Reg32 (r: GPReg32) := mkReg32 (GPReg32_base r).

Definition EAX := (mkNonSPReg32 RAX).
Definition EBX := (mkNonSPReg32 RBX).
Definition ECX := (mkNonSPReg32 RCX).
Definition EDX := (mkNonSPReg32 RDX).
Definition ESI := (mkNonSPReg32 RSI).
Definition EDI := (mkNonSPReg32 RDI).
Definition EBP := (mkNonSPReg32 RBP).
Definition R8D := (mkNonSPReg32 R8).
Definition R9D := (mkNonSPReg32 R9).
Definition R10D := (mkNonSPReg32 R10).
Definition R11D := (mkNonSPReg32 R11).
Definition R12D := (mkNonSPReg32 R12).
Definition R13D := (mkNonSPReg32 R13).
Definition R14D := (mkNonSPReg32 R14).
Definition R15D := (mkNonSPReg32 R15).
Definition ESP := (mkGPReg32 RSP).
Definition EIP := (mkReg32 RIP).

(* Addressable 16-bit slices of above *)
Inductive NonSPReg16 := mkNonSPReg16 (r: NonSPReg64).
Definition NonSPReg16_base r16 := let: mkNonSPReg16 r := r16 in r.
Lemma NonSPReg16_base_inj : injective NonSPReg16_base. Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure NonSPReg16_EqMixin := InjEqMixin NonSPReg16_base_inj.
Canonical Structure NonSPReg16_EqType := Eval hnf in EqType _ NonSPReg16_EqMixin.

Inductive GPReg16 := mkGPReg16 (r: GPReg64).
Definition GPReg16_base r16 := let: mkGPReg16 r := r16 in r.
Lemma GPReg16_base_inj : injective GPReg16_base. Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure GPReg16_EqMixin := InjEqMixin GPReg16_base_inj.
Canonical Structure GPReg16_EqType := Eval hnf in EqType _ GPReg16_EqMixin.

Inductive Reg16 := mkReg16 (r: Reg64).
Definition Reg16_base r16 := let: mkReg16 r := r16 in r.
Lemma Reg16_base_inj : injective Reg16_base. Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure Reg16_EqMixin := InjEqMixin Reg16_base_inj.
Canonical Structure Reg16_EqType := Eval hnf in EqType _ Reg16_EqMixin.

Coercion NonSPReg16_to_GPReg16 (r: NonSPReg16) := mkGPReg16 (NonSPReg16_base r).
Coercion GPReg16_to_Reg16 (r: GPReg16) := mkReg16 (GPReg16_base r).

Definition AX := (mkNonSPReg16 RAX).
Definition BX := (mkNonSPReg16 RBX).
Definition CX := (mkNonSPReg16 RCX).
Definition DX := (mkNonSPReg16 RDX).
Definition SI := (mkNonSPReg16 RSI).
Definition DI := (mkNonSPReg16 RDI).
Definition BP := (mkNonSPReg16 RBP).
Definition R8W := (mkNonSPReg16 R8).
Definition R9W := (mkNonSPReg16 R9).
Definition R10W := (mkNonSPReg16 R10).
Definition R11W := (mkNonSPReg16 R11).
Definition R12W := (mkNonSPReg16 R12).
Definition R13W := (mkNonSPReg16 R13).
Definition R14W := (mkNonSPReg16 R14).
Definition R15W := (mkNonSPReg16 R15).
Definition SP := (mkGPReg16 RSP).
Definition IP := (mkReg16 RIP).


(* Addressable 8-bit slices of above *)
Inductive NonSPReg8 := mkNonSPReg8 (r: NonSPReg64).
Definition NonSPReg8_base r8 := let: mkNonSPReg8 r := r8 in r.
Lemma NonSPReg8_base_inj : injective NonSPReg8_base. Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure NonSPReg8_EqMixin := InjEqMixin NonSPReg8_base_inj.
Canonical Structure NonSPReg8_EqType := Eval hnf in EqType _ NonSPReg8_EqMixin.

Inductive GPReg8 := mkReg8 (r: GPReg64) | AH | BH | CH | DH.
Definition GPReg8_toNat r8 := 
  match r8 with mkReg8 r => GPReg64_toNat r | AH => 16 | BH => 17 | CH => 18 | DH => 19 end.
Lemma GPReg8_toNat_inj : injective GPReg8_toNat. Proof. repeat case => //; case => //.  Qed. 
Canonical Structure GPReg8_EqMixin := InjEqMixin GPReg8_toNat_inj.
Canonical Structure GPReg8_EqType := Eval hnf in EqType _ GPReg8_EqMixin.
Definition Reg8 := GPReg8.

Coercion NonSPReg8_to_Reg8 (r: NonSPReg8) := mkReg8 (NonSPReg8_base r).

Definition AL := (mkNonSPReg8 RAX).
Definition BL := (mkNonSPReg8 RBX).
Definition CL := (mkNonSPReg8 RCX).
Definition DL := (mkNonSPReg8 RDX).
Definition SIL := (mkNonSPReg8 RSI).
Definition DIL := (mkNonSPReg8 RDI).
Definition BPL := (mkNonSPReg8 RBP).
Definition R8L := (mkNonSPReg8 R8).
Definition R9L := (mkNonSPReg8 R9).
Definition R10L := (mkNonSPReg8 R10).
Definition R11L := (mkNonSPReg8 R11).
Definition R12L := (mkNonSPReg8 R12).
Definition R13L := (mkNonSPReg8 R13).
Definition R14L := (mkNonSPReg8 R14).
Definition R15L := (mkNonSPReg8 R15).
Definition SPL := (mkReg8 RSP).

(*
(* Legacy 8-bit registers *)
Inductive Reg8alt := AL|BL|CL|DL|AH|BH|CH|DH.
*)



(*---------------------------------------------------------------------------
    Segment registers
  ---------------------------------------------------------------------------*)
Inductive SegReg := CS | DS | SS | ES | FS | GS.
Definition SegRegToNat r :=  
  match r with CS => 0 | DS => 1 | SS => 2 | ES => 3 | FS => 4 | GS => 5 end. 
Lemma SegRegToNat_inj : injective SegRegToNat. Proof. by repeat case => //. Qed.
Canonical Structure SegRegEqMixin := InjEqMixin SegRegToNat_inj.
Canonical Structure SegRegEqType := Eval hnf in EqType _ SegRegEqMixin.

(*---------------------------------------------------------------------------
    Register pieces: these are the bytes that make up the register state
  ---------------------------------------------------------------------------*)
Definition RegIx := nat (* Could use 'I_8 for stronger typing *). 

Inductive RegPiece := mkRegPiece (r: Reg64) (ix: RegIx).
Definition RegPieceToCode rp :=  let: mkRegPiece r b := rp in (Reg64_toNat r, b). 
Lemma RegPieceToCode_inj : injective RegPieceToCode.
Proof. move => [r1 b1] [r2 b2] /=. move => [H1 H2]. apply Reg64_toNat_inj in H1. by subst. Qed. 

Canonical Structure RegPieceEqMixin := InjEqMixin RegPieceToCode_inj.
Canonical Structure RegPieceEqType := Eval hnf in EqType _ RegPieceEqMixin.

(* This should go somewhere else really *)
Definition getRegPiece (v: QWORD) (ix: RegIx) := 
  match (*val*) ix with
  | 0 => slice 0 8 _ v  
  | 1 => slice 8 8 _ v 
  | 2 => slice 16 8 _ v 
  | 3 => slice 24 8 _ v   
  | 4 => slice 32 8 _ v   
  | 5 => slice 40 8 _ v   
  | 6 => slice 48 8 _ v   
  | 7 => slice 56 8 _ v
  | _ => #0
  end.

(*tnth (bitsToBytes 8 v) ix. *)
Definition putRegPiece (v: QWORD) (ix: RegIx) (b: BYTE) : QWORD :=
  match (*val*) ix with
  | 0 => updateSlice 0 8 _ v b 
  | 1 => updateSlice 8 8 _ v b 
  | 2 => updateSlice 16 8 _ v b 
  | 3 => updateSlice 24 8 _ v b  
  | 4 => updateSlice 32 8 _ v b  
  | 5 => updateSlice 40 8 _ v b  
  | 6 => updateSlice 48 8 _ v b  
  | 7 => updateSlice 56 8 _ v b  
  | _ => v
  end.

Definition Reg8_toRegPiece (r:Reg8) :=
match r with
| mkReg8 r64 => mkRegPiece r64 0
| AH => mkRegPiece RAX 1
| BH => mkRegPiece RBX 1
| CH => mkRegPiece RCX 1
| DH => mkRegPiece RDX 1
end.
  
Require Import bitsprops.
Lemma getRegPiece_ext (v w: QWORD) :
  (forall ix, getRegPiece v ix = getRegPiece w ix) ->
  v = w. 
Proof. move => H. 
have H0:= H 0. 
have H1:= H 1. 
have H2:= H 2. 
have H3:= H 3. 
have H4:= H 4. 
have H5:= H 5. 
have H6:= H 6. 
have H7:= H 7.
simpl in *. 
have P0 := proj2 (sliceEq _ _) H0.
have P1 := proj2 (sliceEq _ _) H1.
have P2 := proj2 (sliceEq _ _) H2.
have P3 := proj2 (sliceEq _ _) H3.
have P4 := proj2 (sliceEq _ _) H4.
have P5 := proj2 (sliceEq _ _) H5.
have P6 := proj2 (sliceEq _ _) H6.
have P7 := proj2 (sliceEq _ _) H7.
apply allBitsEq.
move => i LT. 
case LT8: (i < n8). apply P0 => //. 
case LT16: (i < n16). apply P1; by rewrite LT16 leqNgt LT8. 
case LT24: (i < n24). apply P2; by rewrite LT24 leqNgt LT16. 
case LT32: (i < n32). apply P3; by rewrite LT32 leqNgt LT24. 
case LT40: (i < 40). apply P4; by rewrite LT40 leqNgt LT32. 
case LT48: (i < 48). apply P5; by rewrite LT48 leqNgt LT40. 
case LT56: (i < 56). apply P6; by rewrite LT56 leqNgt LT48. 
case LT64: (i < 64). apply P7; by rewrite LT64 leqNgt LT56. 
by rewrite LT in LT64. 
Qed.

(* 8, 16, 32 or 64 bit registers *)
Definition NonSPReg (s: OpSize) := 
  match s with OpSize1 => NonSPReg8 | OpSize2 => NonSPReg16 | OpSize4 => NonSPReg32 | OpSize8 => NonSPReg64 end.

Definition GPReg (s: OpSize) := 
  match s with OpSize1 => GPReg8 | OpSize2 => GPReg16 | OpSize4 => GPReg32 | OpSize8 => GPReg64 end.

Definition Reg (s: OpSize) :=
  match s with OpSize1 => Reg8 | OpSize2 => Reg16 | OpSize4 => Reg32 | OpSize8 => Reg64 end.
  
Coercion NonSPReg_to_Reg {s} : NonSPReg s -> Reg s  := 
  match s return NonSPReg s -> Reg s with 
  OpSize1 => fun r => r | OpSize2 => fun r => r | OpSize4 => fun r => r | OpSize8 => fun r => r end. 

Coercion GPReg_to_Reg {s} : GPReg s -> Reg s  := 
  match s return GPReg s -> Reg s with 
  OpSize1 => fun r => r | OpSize2 => fun r => r | OpSize4 => fun r => r | OpSize8 => fun r => r end. 

Coercion Reg64_to_Reg (r:Reg64) : Reg OpSize8 := r.
Coercion Reg32_to_Reg (r:Reg32) : Reg OpSize4 := r.
Coercion Reg16_to_Reg (r:Reg16) : Reg OpSize2 := r.
Coercion Reg8_to_Reg (r:GPReg8)   : Reg OpSize1 := r.

Coercion GPReg64_to_GPReg (r:GPReg64) : GPReg OpSize8 := r.
Coercion GPReg32_to_GPReg (r:GPReg32) : GPReg OpSize4 := r.
Coercion GPReg16_to_GPReg (r:GPReg16) : GPReg OpSize2 := r.
Coercion Reg8_to_GPReg (r:GPReg8) : GPReg OpSize1 := r.

(* Universal instruction pointer and stack pointer. EIP/ESP for 32-bit mode, RIP/RSP for 64-bit mode *)
Definition UIP := RIP. 
Definition USP := RSP.

