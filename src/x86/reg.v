(*===========================================================================
    Model for x86 registers
    Note that the EFL register (flags) is treated separately.

    These are registers as used inside instructions, and can refer to
    overlapping sections of the real machine state e.g. AL, AH, AX, EAX
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.choice Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.bitsrep.

(* General purpose registers, excluding ESP *)
(*=NonSPReg *)
Inductive NonSPReg := EAX | EBX | ECX | EDX | ESI | EDI | EBP.
(*=End *)
Definition NonSPRegToNat r :=
  match r with EAX => 0 | ECX => 1 | EDX => 2 | EBX => 3 | EBP => 5 | ESI => 6 | EDI => 7 end.
Lemma NonSPRegToNat_inj : injective NonSPRegToNat. Proof. by case => //; case => //. Qed.
Canonical Structure NonSPRegEqMixin := InjEqMixin NonSPRegToNat_inj.
Canonical Structure NonSPRegEqType := Eval hnf in EqType _ NonSPRegEqMixin.

(* General purpose registers, including ESP *)
(*=Reg *)
Inductive Reg := nonSPReg (r: NonSPReg) | ESP.
(*=End *)
Coercion nonSPReg : NonSPReg >-> Reg.
Definition RegToNat r :=  match r with | ESP => 4 | nonSPReg r => NonSPRegToNat r end.
Lemma RegToNat_inj : injective RegToNat.
Proof. case => //; case => //; case => //; case => //. Qed.
Canonical Structure RegEqMixin := InjEqMixin RegToNat_inj.
Canonical Structure RegEqType := Eval hnf in EqType _ RegEqMixin.

(* All registers, including EIP but excluding EFL *)
(*=AnyReg *)
Inductive AnyReg := regToAnyReg (r: Reg) | EIP.
(*=End *)
Coercion regToAnyReg : Reg >-> AnyReg.
Definition AnyRegToNat r :=  match r with | EIP => 8 | regToAnyReg r => RegToNat r end.
Lemma AnyRegToNat_inj : injective AnyRegToNat.
Proof. case => //; case => //; case => //; case => //; case => //; case => //. Qed.
Canonical Structure AnyRegEqMixin := InjEqMixin AnyRegToNat_inj.
Canonical Structure AnyRegEqType := Eval hnf in EqType _ AnyRegEqMixin.

(* Segment registers *)
Inductive SegReg := CS | DS | SS | ES | FS | GS.
Definition SegRegToNat r :=  
  match r with CS => 0 | DS => 1 | SS => 2 | ES => 3 | FS => 4 | GS => 5 end. 
Lemma SegRegToNat_inj : injective SegRegToNat.
Proof. by case; case. Qed.
Canonical Structure SegRegEqMixin := InjEqMixin SegRegToNat_inj.
Canonical Structure SegRegEqType := Eval hnf in EqType _ SegRegEqMixin.

(* Byte registers *)
Inductive BYTEReg := AL|BL|CL|DL|AH|BH|CH|DH.

(* 16-bit legacy registers; wrap underlying 32-bit registers *)
Inductive WORDReg := mkWordReg (r:Reg).
Notation AX := (mkWordReg EAX).
Notation BX := (mkWordReg EBX).
Notation CX := (mkWordReg ECX).
Notation DX := (mkWordReg EDX).
Notation SI := (mkWordReg ESI).
Notation DI := (mkWordReg EDI).
Notation BP := (mkWordReg EBP).
Notation SP := (mkWordReg ESP).

Definition WORDRegToReg (wr:WORDReg):Reg := let: mkWordReg r := wr in r.
Lemma WORDRegToReg_inj : injective WORDRegToReg.
Proof. by move => [x] [y] /= ->. Qed. 
Canonical Structure WORDRegEqMixin := InjEqMixin WORDRegToReg_inj.
Canonical Structure WORDRegEqType := Eval hnf in EqType _ WORDRegEqMixin.

(* Standard numbering of registers *)
Definition natToReg n : option Reg :=
  match n return option Reg with
  | 0 => Some (EAX:Reg)
  | 1 => Some (ECX:Reg)
  | 2 => Some (EDX:Reg)
  | 3 => Some (EBX:Reg)
  | 4 => Some (ESP:Reg)
  | 5 => Some (EBP:Reg)
  | 6 => Some (ESI:Reg)
  | 7 => Some (EDI:Reg)
  | _ => None
  end.

Lemma roundtripReg : forall r, natToReg (RegToNat r) = Some r.
Proof. case. by case. done. Qed.

(* Reg is a choiceType and a countType *)
Definition Reg_countMixin := CountMixin roundtripReg.
Definition Reg_choiceMixin := CountChoiceMixin Reg_countMixin.
Canonical Reg_choiceType :=  Eval hnf in ChoiceType _ Reg_choiceMixin.
Canonical Reg_countType  :=  Eval hnf in CountType _ Reg_countMixin.

(* Reg is a finType *)
Lemma Reg_enumP :
  Finite.axiom [:: EAX:Reg; EBX:Reg; ECX:Reg; EDX:Reg; ESI:Reg; EDI:Reg; EBP:Reg; ESP].
Proof. case;  [by case | done]. Qed.

Definition Reg_finMixin := Eval hnf in FinMixin Reg_enumP.
Canonical Reg_finType   := Eval hnf in FinType _ Reg_finMixin.

(* Standard numbering of registers *)
Definition natToAnyReg n :=
  match natToReg n with
  | Some r => Some (regToAnyReg r)
  | None => match n with 8 => Some EIP | _ => None end
  end.

Lemma roundtripAnyReg : forall r, natToAnyReg (AnyRegToNat r) = Some r.
Proof. case. case; [case; by constructor | done]. done. Qed.

(* AnyReg is a choiceType and a countType *)
Definition AnyReg_countMixin := CountMixin roundtripAnyReg.
Definition AnyReg_choiceMixin := CountChoiceMixin AnyReg_countMixin.
Canonical AnyReg_choiceType := Eval hnf in ChoiceType _ AnyReg_choiceMixin.
Canonical AnyReg_countType  := Eval hnf in CountType  _ AnyReg_countMixin.

(* AnyReg is a finType *)
Lemma AnyReg_enumP :
  Finite.axiom [:: EAX:AnyReg; EBX:AnyReg; ECX:AnyReg;
                   EDX:AnyReg; ESI:AnyReg; EDI:AnyReg; EBP:AnyReg; ESP:AnyReg; EIP].
Proof. case; [case; [case; done | done] | done]. Qed.

Definition AnyReg_finMixin := Eval hnf in FinMixin AnyReg_enumP.
Canonical AnyReg_finType :=  Eval hnf in FinType _ AnyReg_finMixin.

(*---------------------------------------------------------------------------
    Register pieces: these are the bytes that make up the register state
  ---------------------------------------------------------------------------*)
Inductive RegIx := RegIx0 | RegIx1 | RegIx2 | RegIx3.
Definition RegIxToNat ix := match ix with RegIx0 => 0 | RegIx1 => 1 | RegIx2 => 2 | RegIx3 => 3 end.
Lemma RegIxToNat_inj : injective RegIxToNat.
Proof. by case; case. Qed.

Canonical Structure RegIxEqMixin := InjEqMixin RegIxToNat_inj.
Canonical Structure RegIxEqType := Eval hnf in EqType _ RegIxEqMixin.

Inductive RegPiece := AnyRegPiece (r: AnyReg) (ix: RegIx).
Definition RegPieceToCode rp :=  let: AnyRegPiece r b := rp in (AnyRegToNat r, RegIxToNat b). 
Lemma RegPieceToCode_inj : injective RegPieceToCode.
Proof. by move => [r1 b1] [r2 b2] /= [/AnyRegToNat_inj -> /RegIxToNat_inj ->]. Qed. 

Canonical Structure RegPieceEqMixin := InjEqMixin RegPieceToCode_inj.
Canonical Structure RegPieceEqType := Eval hnf in EqType _ RegPieceEqMixin.

(* This should go somewhere else really *)
Definition getRegPiece (v: DWORD) (ix: RegIx)  := 
  match ix with 
  | RegIx0 => slice 0 8 _ v 
  | RegIx1 => slice 8 8 _ v 
  | RegIx2 => slice 16 8 _ v 
  | RegIx3 => slice 24 8 _ v 
  end.

Definition putRegPiece (v: DWORD) (ix: RegIx) (b: BYTE) : DWORD :=
  match ix with
  | RegIx0 => updateSlice 0 8 _ v b 
  | RegIx1 => updateSlice 8 8 _ v b 
  | RegIx2 => updateSlice 16 8 _ v b 
  | RegIx3 => updateSlice 24 8 _ v b  
  end.
  
Require Import bitsprops.
Lemma getRegPiece_ext (v w: DWORD) :
  getRegPiece v RegIx0 = getRegPiece w RegIx0 ->
  getRegPiece v RegIx1 = getRegPiece w RegIx1 ->
  getRegPiece v RegIx2 = getRegPiece w RegIx2 ->
  getRegPiece v RegIx3 = getRegPiece w RegIx3 ->
  v = w. 
Proof. move => H0 H1 H2 H3.
rewrite /getRegPiece in H0. 
rewrite /getRegPiece in H1. 
rewrite /getRegPiece in H2. 
rewrite /getRegPiece in H3. 
have S0 := proj2 (sliceEq _ _) H0. 
have S1 := proj2 (sliceEq _ _) H1. 
have S2 := proj2 (sliceEq _ _) H2. 
have S3 := proj2 (sliceEq _ _) H3. 
apply allBitsEq. 
move => i LT. 
case LT8: (i < n8). apply (S0 _ LT8). 
case LT16: (i < n16). apply S1. by rewrite LT16 leqNgt LT8. 
case LT24: (i < n24). apply S2. by rewrite LT24 leqNgt LT16. 
apply S3. by rewrite LT leqNgt LT24. 
Qed.

Definition BYTERegToRegPiece (r:BYTEReg) :=
match r with
| AL => AnyRegPiece EAX RegIx0
| AH => AnyRegPiece EAX RegIx1
| BL => AnyRegPiece EBX RegIx0
| BH => AnyRegPiece EBX RegIx1
| CL => AnyRegPiece ECX RegIx0
| CH => AnyRegPiece ECX RegIx1
| DL => AnyRegPiece EDX RegIx0
| DH => AnyRegPiece EDX RegIx1
end.

(* BYTE, WORD or DWORD register, not including EIP *)
Definition VReg (s: OpSize) := 
  match s with OpSize1 => BYTEReg | OpSize2 => WORDReg | OpSize4 => Reg end.

Definition VRegAny (s: OpSize) :=
  match s with OpSize1 => BYTEReg | OpSize2 => WORDReg | OpSize4 => AnyReg end.
  
Coercion VRegToVRegAny {s} : VReg s -> VRegAny s  := 
  match s return VReg s -> VRegAny s with OpSize1 => fun r => r | OpSize2 => fun r => r | OpSize4 => fun r => r end. 

Coercion RegToVReg (r:Reg) : VReg OpSize4 := r.
Coercion WORDRegToVReg (r:WORDReg) : VReg OpSize2 := r.
Coercion BYTERegToVReg (r:BYTEReg) : VReg OpSize1 := r.
Coercion AnyRegToVRegAny (r: AnyReg) : VRegAny OpSize4 := r.
