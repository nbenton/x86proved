(*===========================================================================
    State of the registers
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.finfun .
Require Import x86proved.x86.reg x86proved.bitsrep x86proved.update.
Local Open Scope update_scope.

(* State of the registers, including RIP and flags *)
(* Lookup is just function application *)
(*=RegState *)
Definition RegState := Reg64 -> QWORD.
(*=End *)

(* Avoid == to permit extraction *)
Instance RegStateUpdateOps : UpdateOps RegState Reg64 QWORD :=
  fun rs r v => fun r' => if r == r' then v else rs r'.

Lemma setThenGetDistinct r1 v r2 (rs: RegState) :
  ~~ (r1 == r2) -> (rs !r1:=v) r2 = rs r2.
Proof. move => neq. rewrite /update /RegStateUpdateOps. by rewrite (negbTE neq). Qed.

Lemma setThenGetSame r v rs : (rs !r:=v) r = v.
Proof. rewrite /update /RegStateUpdateOps.
by rewrite (introT (eqP) (refl_equal _)).
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Instance RegStateUpdate : Update RegState Reg64 QWORD.
apply Build_Update.
(* Same register *)
move => rs r v w. rewrite /update /RegStateUpdateOps.
apply functional_extensionality => r'. by case: (r == r').
(* Different register *)
move => rs r1 r2 v1 v2 neq. rewrite /update /RegStateUpdateOps.
apply functional_extensionality => r.
case E1: (r2 == r).
case E2: (r1 == r). rewrite (elimT (eqP) E1) in neq.
rewrite (elimT (eqP) E2) in neq. done. done.
done.
Qed.

Definition initialReg : RegState := fun _ => #0.

Require Import Coq.Strings.String.
(* TODO: other 8 regs *)
Definition regStateToString (rs:RegState) :=
  (" RIP=" ++ toHex (rs RIP) ++
   " RSP=" ++ toHex (rs RSP) ++
   " RBP=" ++ toHex (rs RBP) ++
   " RAX=" ++ toHex (rs RAX) ++
   " RBX=" ++ toHex (rs RBX) ++
   " RCX=" ++ toHex (rs RCX) ++
   " RDX=" ++ toHex (rs RDX) ++
   " RSI=" ++ toHex (rs RSI) ++
   " RDI=" ++ toHex (rs RDI) ++
   " RBP=" ++ toHex (rs RBP)
   )%string.
