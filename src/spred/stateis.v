(*===========================================================================
    stateIs predicate for registers and flags
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.pfun x86proved.x86.reg x86proved.x86.mem x86proved.x86.flags.
Require Import x86proved.pmap x86proved.pmapprops x86proved.x86.addr x86proved.spred.core x86proved.spred.tactics.
Require Import Coq.Setoids.Setoid x86proved.charge.csetoid Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.FunctionalExtensionality.

Local Opaque SABIOps.

Global Coercion lbool (b:bool) := lpropand b ltrue.

(*===========================================================================
    "is" predicates on registers and flags
  ===========================================================================*)

Definition regPieceIs r v : SPred := eq_pred (addRegPieceToPState emptyPState r v).
Definition flagIs f b : SPred := eq_pred (addFlagToPState emptyPState f b).
Definition segRegIs r w : SPred := eq_pred (addSegRegToPState emptyPState r w).

Definition reg64Is (r:Reg64) (v:QWORD) : SPred :=
  let pi i := regPieceIs (mkRegPiece r i) (getRegPiece v i) in
   pi 0 ** pi 1 ** pi 2 ** pi 3 ** pi 4 ** pi 5 ** pi 6 ** pi 7.

(* @TODO: get rid of this silly zero extension *)
Definition reg32Is (r:Reg32) (v:DWORD) : SPred :=
  let pi i := regPieceIs (mkRegPiece (Reg32_base r) i) (getRegPiece (zeroExtend 32 v) i) in
   pi 0 ** pi 1 ** pi 2 ** pi 3.

Definition reg16Is (r:Reg16) (v:WORD) : SPred :=
   regPieceIs (mkRegPiece (Reg16_base r) 0) (slice 0 8 8 v)
** regPieceIs (mkRegPiece (Reg16_base r) 1) (slice 8 8 0 v).

Definition reg8Is (r:Reg8) (v:BYTE) : SPred :=
   regPieceIs (Reg8_toRegPiece r) v.

Inductive RegOrFlag :=
| RegOrFlagR s :> Reg s -> RegOrFlag
| RegOrFlagS :> SegReg -> RegOrFlag
| RegOrFlagF :> Flag -> RegOrFlag.

Definition RegOrFlag_target rf :=
match rf with
| RegOrFlagR s _   => VWORD s
| RegOrFlagS _     => WORD
| RegOrFlagF _     => FlagVal
end.

Definition stateIs (x: RegOrFlag) : RegOrFlag_target x -> SPred :=
match x with
| RegOrFlagS r => segRegIs r
| RegOrFlagR OpSize1 r => reg8Is r
| RegOrFlagR OpSize2 r => reg16Is r
| RegOrFlagR OpSize4 r => reg32Is r
| RegOrFlagR OpSize8 r => reg64Is r
| RegOrFlagF f => flagIs f
end.

Implicit Arguments stateIs [].

Definition stateIsAny x := lexists (stateIs x).

Notation "x '~=' v" := (stateIs x v) (at level 70, no associativity, format "x '~=' v") : spred_scope.
Notation "x '?'" := (stateIsAny x) (at level 2, format "x '?'"): spred_scope.

Hint Unfold VWORD RegOrFlag_target : spred.
(** When dealing with logic, we want to reduce [stateIsAny] and similar to basic building blocks. *)
Hint Unfold stateIsAny : finish_logic_unfolder.

Instance flagIsEquiv_m :
  Proper (eq ==> eq ==> csetoid.equiv ==> iff) flagIs.
Proof.
  intros n m Hneqm f g Hbeqc p q Hpeqq; subst.
  split; simpl; rewrite <- Hpeqq; tauto.
Qed.

Instance StrictlyExactRegPieceIs r v: StrictlyExact (regPieceIs r v).
Proof. move => s s'. simpl. by move ->. Qed.

Instance StrictlyExactFlagIs f v: StrictlyExact (flagIs f v).
Proof. move => s s'. simpl. by move ->. Qed.

Instance StrictlyExactByteIs p v: StrictlyExact (byteIs p v).
Proof. move => s s'. simpl. by move ->. Qed.

Instance StrictlyExactRegIs r v: StrictlyExact (reg64Is r v).
Proof. rewrite /reg64Is. do 7 (apply StrictlyExactSep; first apply StrictlyExactRegPieceIs).
apply StrictlyExactRegPieceIs. Qed.

(*---------------------------------------------------------------------------
    Some lemmas about the domains of primitive points-to-like predicates
  ---------------------------------------------------------------------------*)
Open Scope spred_scope.
Local Transparent ILFun_Ops lentails sepILogicOps.

Lemma regPieceIs_same (r:RegPiece) v1 v2 : regPieceIs r v1 ** regPieceIs r v2 |-- lfalse.
Proof. move => s [s1 [s2 [H1 [H1a H1b]]]].
simpl in H1a, H1b. rewrite <-H1a in H1. rewrite <-H1b in H1.
rewrite /sa_mul/PStateSepAlgOps/= in H1.
specialize (H1 Registers r). simpl in H1.
destruct (s Registers r); rewrite eq_refl in H1.
destruct H1; by destruct H.
by destruct H1.
Qed.

Lemma sepRev4 P Q R S : P ** Q ** R ** S -|- S ** R ** Q ** P.
Proof. rewrite (sepSPC P). rewrite (sepSPC Q). rewrite (sepSPC R).
by rewrite !sepSPA. Qed.


Lemma regIs_same s (r:Reg s) (v1 v2:VWORD s) : r ~= v1 ** r ~= v2 |-- lfalse.
Proof. destruct s. 
- apply regPieceIs_same. 
- rewrite /stateIs/reg16Is. 
  rewrite -(sepSPC (regPieceIs (mkRegPiece (Reg16_base r) 1) _)). 
  rewrite sepSPA. setoid_rewrite <-sepSPA at 2. 
  rewrite -> (@regPieceIs_same (mkRegPiece _ _)).
  rewrite !sepSP_falseL.
  by rewrite !sepSP_falseR.  
- rewrite /stateIs/reg32Is. 
  rewrite sepRev4. rewrite sepSPA.
  rewrite sepRev4. rewrite -!sepSPA. rewrite -> (@regPieceIs_same (mkRegPiece _ 0)).
  by rewrite !sepSP_falseL. 
- rewrite /stateIs/reg64Is. 
  rewrite sepRev4. rewrite sepSPA.
  rewrite sepRev4. rewrite -!sepSPA. rewrite -> (@regPieceIs_same (mkRegPiece _ 0)).
  by rewrite !sepSP_falseL. 
Qed.

Lemma flagIs_same (f:Flag) v1 v2 : f ~= v1 ** f ~= v2 |-- lfalse.
Proof.  move => s [s1 [s2 [H1 [H1a H1b]]]].
simpl in H1a, H1b. rewrite <-H1a in H1. rewrite <-H1b in H1.
rewrite /sa_mul/PStateSepAlgOps/= in H1.
specialize (H1 Flags f). simpl in H1.
destruct (s Flags f); rewrite eq_refl in H1.
destruct H1; by destruct H.
by destruct H1.
Qed.

(* We don't want simpl to unfold this *)
Global Opaque stateIs.

(* Disjointness for registers, flags and bytes *)
Lemma regIs_disjoint s (r1 r2: Reg s) v1 v2 : r1 ~= v1 ** r2 ~= v2 |-- r1 <> r2 /\\ (r1 ~= v1 ** r2 ~= v2).
Proof. destruct s;
(case E: (r1 == r2); [(rewrite (eqP E); by setoid_rewrite regIs_same at 1) | ssplit => H; [by rewrite H eq_refl in E| done]]). 
Qed. 

Lemma flagIs_disjoint (f1 f2: Flag) v1 v2 : f1 ~= v1 ** f2 ~= v2 |-- f1 <> f2 /\\ (f1 ~= v1 ** f2 ~= v2).
Proof. case E: (f1 == f2). rewrite (eqP E). by setoid_rewrite flagIs_same at 1.
ssplit; last done. move => H. by rewrite H eq_refl in E.
Qed.

