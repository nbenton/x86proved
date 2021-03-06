Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.spectac x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.basic x86proved.x86.macros x86proved.charge.ilogic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.

Definition splits (p q r: DWORD) (vs ws: seq DWORD) :=
  p -- q :-> vs ** q -- r :-> ws.

Definition nextCode := (ADD ESI, 4). 
Definition nextSpec code := 
  Forall (p q r: DWORD), Forall vs w ws, 
  basic (splits p q r vs (w::ws) ** ESI ~= q) code 
        (splits p (q+#4) r (vs++[::w]) ws ** ESI ~= (q+#4)) @ OSZCP?.

Lemma nextCorrect : |-- nextSpec nextCode. 
Proof. rewrite /nextSpec/nextCode. specintros => *. autorewrite with push_at.
basic apply *.
rewrite /splits. 
rewrite -> (seqFixedMemIsCons' _). rewrite seqMemIsCat pairMemIsPair'. sbazooka. 
rewrite -> seqMemIsCons. sbazooka. 
rewrite -> seqMemIsNil. sbazooka. 
Qed. 

Definition opSizeToNat s := match s with OpSize1 => 1 | OpSize2 => 2 | OpSize4 => 4 end.

Lemma MOV_RM0aux_rule s (r1: VReg s) (r2:Reg)  (pd:DWORD) (v1 v2: VWORD s) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd -- (pd+#opSizeToNat s) :-> v2)
            (MOV r1, [r2]) 
            (r1 ~= v2 ** r2 ~= pd ** pd -- (pd+#opSizeToNat s) :-> v2).
Proof. rewrite ->memIsLe at 1. specintros => LE. rewrite ->memIs_pointsTo at 1.
destruct s; basic apply *; rewrite -> (fixedMemIs_pointsTo (n:=_)) => //; reflexivity. 
Qed.

Global Instance: forall s (r1: VReg s) (r2: Reg), instrrule (MOV r1, [r2]) := @MOV_RM0aux_rule.

Lemma MOV_M0Raux_rule s (r1: VReg s) (r2:Reg)  (pd:DWORD) (v1 v2: VWORD s) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd -- (pd+#opSizeToNat s) :-> v2)
            (MOV [r2], r1) 
            (r1 ~= v1 ** r2 ~= pd ** pd -- (pd+#opSizeToNat s) :-> v1).
Proof. rewrite -> memIsLe at 1. specintros => LE. rewrite -> memIs_pointsTo at 1. 
destruct s; basic apply *; rewrite -> (fixedMemIs_pointsTo (n:=_)) => //; reflexivity. 
Qed.
Global Instance: forall s (r1: VReg s) (r2: Reg), instrrule (MOV [r2], r1) := @MOV_M0Raux_rule.

Definition getCode (dst:Reg):program := (MOV dst, [ESI]). 
Definition getSpec (dst:Reg) code :=   
  Forall (p q r: DWORD), Forall vs w ws oldv, 
  basic 
  (dst ~= oldv)
  code 
  (dst ~= w) @ (splits p q r vs (w::ws) ** ESI ~= q).

Hint Unfold readVWORD opSizeToNat : instrrules_all.

Lemma getCorrect (dst: Reg):
  |-- getSpec dst (getCode dst). 
Proof.
rewrite /getSpec/getCode. specintros => p q r vs w ws oldv. autorewrite with push_at.
rewrite /splits. rewrite -> (seqFixedMemIsCons' _).
basic apply (MOV_RM0aux_rule (s:=OpSize4)). 
Qed. 

Lemma putCorrect (p q r: DWORD) vs w ws oldv :
  |-- basic 
  (splits p q r vs (oldv::ws) ** ESI ~= q ** EAX ~= w)
  (MOV [ESI], EAX)
  (splits p q r vs (w::ws) ** ESI ~= q ** EAX ~= w).
Proof.
rewrite /splits. do 2 rewrite -> (seqFixedMemIsCons' _).
basic apply (MOV_M0Raux_rule (s:=OpSize4)). 
Qed. 

Lemma atEndCorrect (p q r: DWORD) (vs ws: seq DWORD):
  |-- basic
  (splits p q r vs ws ** ESI ~= q ** ZF? ** OF? ** SF? ** CF? ** PF?)
  (CMP ESI, r)
  (splits p q r vs ws ** ESI ~= q ** ZF ~= (if ws is nil then true else false) ** OF? ** SF? ** CF? ** PF?).
Proof. rewrite /splits. destruct ws. 
- rewrite seqMemIsNil. 
  specintros => [[->]]. basicCMP_ZC. 
- rewrite -> (seqFixedMemIsConsNE (n:=4)) at 1 => //.  
  specintros =>/negbTE <-. basicCMP_ZC. 
  (* Why doesn't it pick this up automatically? *) apply FixedMemIsDWORD. 
Qed. 

