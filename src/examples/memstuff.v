Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.spectac x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor x86proved.x86.basic x86proved.x86.macros x86proved.charge.ilogic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.

Definition splits (p q r: ADDR) (vs ws: seq ADDR) :=
  p -- q :-> vs ** q -- r :-> ws.

Definition nextCode := (ADD RSI, BOPArgI _ #8). 
Definition nextSpec code := 
  Forall (p q r: ADDR), Forall vs w ws, 
  basic (splits p q r vs (w::ws) ** RSI ~= q) code empOP
        (splits p (q+#8) r (vs++[::w]) ws ** RSI ~= (q+#8)) @ OSZCP?.

Lemma nextCorrect : |-- nextSpec nextCode. 
Proof. rewrite /nextSpec/nextCode. specintros => *. autorewrite with push_at.
basic apply *.
rewrite /splits. 
rewrite -> (seqFixedMemIsCons' _). rewrite seqMemIsCat pairMemIsPair'. rewrite signExtend_fromNat => //.
rewrite sepSPC. sbazooka. rewrite -> seqMemIsCons. sbazooka. 
rewrite -> seqMemIsNil. sbazooka. reflexivity. 
Qed. 


Definition getCode (dst:GPReg64):program := (MOV dst, QWORD PTR [RSI]). 
Definition getSpec (dst:GPReg64) code :=   
  Forall (p q r: ADDR), Forall vs w ws oldv, 
  basic 
  (dst ~= oldv)
  code 
  empOP
  (dst ~= w) @ (splits p q r vs (w::ws) ** RSI ~= q).

Hint Unfold readVWORD opSizeToNat : instrrules_all.

Lemma getCorrect (dst: GPReg64):
  |-- getSpec dst (getCode dst). 
Proof.
rewrite /getSpec/getCode. specintros => p q r vs w ws oldv. autorewrite with push_at.
rewrite /splits. rewrite -> (seqFixedMemIsCons' _).
rewrite /pointsTo. Hint Rewrite ->signExtend_fromNat : ssimpl. 
rewrite ->(@memIsLe _ _ q) at 1. specintros => LE. 
attempt basic apply *.
rewrite /pointsTo. sbazooka. 
ssimpl. rewrite -> (fixedMemIs_pointsTo (n:=_)) => //. reflexivity. 
Qed. 

Lemma putCorrect (p q r: ADDR) vs w ws oldv :
  |-- basic 
  (splits p q r vs (oldv::ws) ** RSI ~= q ** RAX ~= w)
  (MOV QWORD PTR [RSI], RAX)
  empOP
  (splits p q r vs (w::ws) ** RSI ~= q ** RAX ~= w).
Proof.
rewrite /splits. do 2 rewrite -> (seqFixedMemIsCons' _).
rewrite ->(@memIsLe _ _ q) at 1. specintros => LE. 
attempt basic apply *.  
rewrite /pointsTo. sbazooka.
ssimpl. rewrite -> (fixedMemIs_pointsTo (n:=_)) => //. reflexivity. 
Qed. 

Lemma atEndCorrect (r:GPReg64) (p q a: ADDR) (vs ws: seq ADDR):
  |-- basic
  (splits p q a vs ws ** r ~= a ** RSI ~= q ** ZF? ** OF? ** SF? ** CF? ** PF?)
  (CMP RSI, r)
  empOP
  (splits p q a vs ws ** r ~= a ** RSI ~= q ** ZF ~= (if ws is nil then true else false) ** OF? ** SF? ** CF? ** PF?).
Proof. rewrite /splits. destruct ws. 
- rewrite seqMemIsNil. 
  specintros => [[->]]. basicCMP_ZC. 
- rewrite -> (seqFixedMemIsConsNE (n:=8)) at 1 => //.  
  specintros =>/negbTE <-. basicCMP_ZC. 
  (* Why doesn't it pick this up automatically? *) apply FixedMemIsQWORD. 
Qed. 
