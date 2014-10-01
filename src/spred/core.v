(*===========================================================================
    Predicates over system state: actually predicates over a subset of
    processor state, in order to define separating conjunction nicely.
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.pfun x86proved.x86.reg x86proved.x86.mem x86proved.x86.flags.
Require Import x86proved.pmap x86proved.pmapprops x86proved.x86.addr.
Require Import Coq.Setoids.Setoid x86proved.charge.csetoid Coq.Classes.Morphisms.


(* Importing this file really only makes sense if you also import ilogic, so we
   force that. *)
Require Export x86proved.charge.ilogic x86proved.charge.bilogic x86proved.ilogicss x86proved.charge.sepalg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.FunctionalExtensionality.

(*---------------------------------------------------------------------------
    Define partial states and lift definitions and lemmas from partial functions

    A partial state consists of
    - a partial register file
    - a partial memory map
    - a partial flag file
  ---------------------------------------------------------------------------*)

Inductive Frag := Registers | Memory | Flags.
Definition fragDom d :=
  match d with
  | Registers => RegPiece
  | Memory => ADDR
  | Flags => Flag
  end.

Definition fragTgt d :=
  match d with
  | Registers => BYTE
    (* None = "memory not mapped" or "memory inaccessible".
       Access to such memory should cause a trap handler to be executed *)
  | Memory => option BYTE

    (* FlagUnspecified = "unspecified", and might not even be stable
       (e.g. two reads of the flag won't necessarily be consistent) *)
  | Flags => FlagVal
  end.

(* None = "not described" for the purposes of separation logic *)
Definition PState := forall f: Frag, fragDom f -> option (fragTgt f).

Structure StateFrag : Type := {frag:Frag; carrier:>Type}.
Canonical Structure Reg64StateFrag := @Build_StateFrag Registers Reg64.
Canonical Structure NonSPReg64StateFrag := @Build_StateFrag Registers NonSPReg64.
Canonical Structure GPReg64StateFrag := @Build_StateFrag Registers GPReg64.
Canonical Structure FlagStateFrag := Build_StateFrag Flags Flag.

Definition fragOf {sf: StateFrag} (x: carrier sf) := frag sf.

Definition emptyPState : PState := fun _ => empFun _.

Definition addRegPieceToPState (s:PState) (rp:RegPiece) (v:BYTE) : PState :=
  fun (f:Frag) =>
  match f as f in Frag return fragDom f -> option (fragTgt f) with
  | Registers => fun rp' => if rp == rp' then Some v else s Registers rp'
  | Flags => s Flags
  | Memory => s Memory
  end.

Definition addFlagToPState (s:PState) f v : PState :=
  fun (fr:Frag) =>
  match fr as fr in Frag return fragDom fr -> option (fragTgt fr) with
  | Registers => s Registers
  | Flags => fun f' => if f == f' then Some v else s Flags f'
  | Memory => s Memory
  end.

Definition addBYTEToPState (s:PState) (p:ADDR) b : PState :=
  fun (fr:Frag) =>
  match fr as fr in Frag return fragDom fr -> option (fragTgt fr) with
  | Memory => fun p' => if p == p' then Some (Some b) else s Memory p'
  | Registers => s Registers
  | Flags => s Flags
  end.

(*
Definition addToPState (f:Frag) (s: PState) : fragDom f -> fragTgt f -> PState :=
  match f with (* as f in Frag return fragDom f -> option (fragTgt f) with *)
  | Registers => fun r v => addRegToPState s r v
  | Flags => fun f v => addFlagToPState s f v
  | Memory => fun p v => addBYTEToPState s p v
  end.

Definition genericAddToPState (f:StateFrag) (s: PState) (x: carrier f) (v: fragTgt (frag f)) := @addToPState (frag f) s x v.

Check (fun s => genericAddToPState s EAX #0).
Definition undefRegToPState s r :=
  mkPState (fun r' => if r==r' then None else pregisters s r') (pmemory s) (pflags s) (ptrace s).
*)

(*
Definition addGenRegToPState s r v :=
  mkPState (fun r' => if r==r' then v else pregisters s r') (pmemory s) (pflags s) (ptrace s).
*)


Definition extendState (s1 s2: PState) : PState := fun f => extend (s1 f) (s2 f).
Definition stateIncludedIn (s1 s2: PState) := forall f, includedIn (s1 f) (s2 f).

Lemma stateIncludedIn_trans (s1 s2 s3:PState) :
  stateIncludedIn s1 s2 -> stateIncludedIn s2 s3 -> stateIncludedIn s1 s3.
Proof. move => H1 H2 f. by apply: includedIn_trans. Qed.

(*
Lemma stateIncludedIn_modReg : forall (s1 s2:PState) (r:AnyReg) x, stateIncludedIn s1 s2 ->
stateIncludedIn (addRegToPState s1 r x) (addRegToPState s2 r x).
Proof.
rewrite /stateIncludedIn /addRegToPState /includedIn; simpl; move => s1 s2 r v Hincl.
destruct Hincl.
split. move => r0 y.
assert (r === r0 \/ r != r0).
destruct r; destruct r0; auto.
destruct r; destruct r0; auto.
destruct n; destruct n0; auto.
destruct H1 as [H1 | H1].
rewrite H1; auto.
rewrite (negPf H1). auto.
auto.
Qed.

Lemma stateIncludedIn_modGenReg : forall (s1 s2:PState) (r:AnyReg) v, stateIncludedIn s1 s2 ->
stateIncludedIn (addGenRegToPState s1 r v) (addGenRegToPState s2 r v).
Proof.
rewrite /stateIncludedIn /addGenRegToPState /includedIn; simpl; move => s1 s2 r v Hincl.
destruct Hincl.
split. move => r0.
assert (r === r0 \/ r != r0).
destruct r; destruct r0; auto.
destruct r; destruct r0; auto.
destruct n; destruct n0; auto.
destruct H1 as [H1 | H1].
rewrite H1; auto.
rewrite (negPf H1). auto.
auto.
Qed.
*)

Definition stateSplitsAs (s s1 s2: PState) := forall f, splitsAs (s f) (s1 f) (s2 f).

Lemma stateSplitsAsIncludes s s1 s2 :
  stateSplitsAs s s1 s2 -> stateIncludedIn s1 s /\ stateIncludedIn s2 s.
Proof. move => H.
split => f. apply (proj1 (splitsAsIncludes (H f))). apply (proj2 (splitsAsIncludes (H f))).
Qed.

Lemma stateSplitsAsExtendL s s1 s2 s3 s4 : stateSplitsAs s s1 s2 -> stateSplitsAs s2 s3 s4 ->
  stateSplitsAs s (extendState s1 s3) s4.
Proof. move => H1 H2 f. by apply: splitsAsExtendL. Qed.

Lemma stateSplitsAsExtends s s1 s2 : stateSplitsAs s s1 s2 -> s = extendState s1 s2.
Proof.
  move => H.
  extensionality f.
  extensionality x.
  exact: splitsAsExtend.
Qed.

Lemma stateSplitsAs_s_emp_s s : stateSplitsAs s emptyPState s.
Proof. move => f. apply: splitsAs_f_emp_f. Qed.

Lemma stateSplitsAs_s_s_emp s : stateSplitsAs s s emptyPState.
Proof. move => f. apply: splitsAs_f_f_emp. Qed.

Lemma stateSplitsAs_s_emp_t s t : stateSplitsAs s emptyPState t -> s = t.
Proof. move => H. extensionality f.
apply: functional_extensionality. apply: splitsAs_f_emp_g. apply: H.
Qed.

Lemma stateSplitsAs_s_t_emp s t : stateSplitsAs s t emptyPState -> s = t.
Proof. move => H. extensionality f.
apply: functional_extensionality. apply: splitsAs_f_g_emp. apply: H.
Qed.

Lemma stateSplitsAs_s_t_s s t: stateSplitsAs s t s -> t = emptyPState.
Proof. move => H. extensionality f.
apply: functional_extensionality. apply: splitsAs_f_g_f. apply H.
Qed.

Lemma stateSplitsAs_s_s_t s t: stateSplitsAs s s t -> t = emptyPState.
Proof. move => H. extensionality f.
apply: functional_extensionality. apply: splitsAs_f_f_g. apply H.
Qed.

Lemma stateSplitsAsIncludedInSplitsAs f f1 f2 g :
    stateSplitsAs f f1 f2 -> stateIncludedIn f g -> exists g1, exists g2,
    stateSplitsAs g g1 g2 /\ stateIncludedIn f1 g1 /\ stateIncludedIn f2 g2.
Proof. move => H1 H2.
exists f1.
set g2 := fun fr => fun x => if f1 fr x is Some _ then None else if f2 fr x is Some y then Some y else g fr x.
exists g2.
split => //.
move => fr. apply (splitsAsIncludedInSplitsAs (H1 fr) (H2 fr)).
split => //.
move => fr. apply (splitsAsIncludedInSplitsAs (H1 fr) (H2 fr)).
Qed.

(* a version more faithful to [splitsAsIncludedInSplitsAs] *)
Lemma stateSplitsAsIncludedInSplitsAs' (f f1 f2 g: PState) :
  stateSplitsAs f f1 f2 -> stateIncludedIn f g ->
  exists g2,
  stateSplitsAs g f1 g2 /\ stateIncludedIn f2 g2.
Proof.
  move=> Hsplit Hinc.
  exists (fun fr => fun x => if f1 fr x is Some _ then None else if f2 fr x is Some y then Some y else g fr x).
  split => fr; by have [? ?] := splitsAsIncludedInSplitsAs (Hsplit fr) (Hinc fr).
Qed.

Lemma stateSplitsAs_functional s1 s2 h i : stateSplitsAs h s1 s2 -> stateSplitsAs i s1 s2 -> h = i.
Proof. move => H1 H2.
extensionality f.
specialize (H1 f). specialize (H2 f).
have H:= splitsAs_functional H1 H2.
apply: functional_extensionality.
move => x. by specialize (H x).
Qed.

Lemma stateSplitsAs_functionalArg s s1 s2 s3 : stateSplitsAs s s2 s1 -> stateSplitsAs s s3 s1 -> s2 = s3.
Proof. move => H1 H2.
extensionality f.
specialize (H1 f). specialize (H2 f).
have H := splitsAs_functionalArg H1 H2.
apply: functional_extensionality.
move => x. by specialize (H x).
Qed.

Lemma stateSplitsAs_commutative s s1 s2 :
  stateSplitsAs s s1 s2 -> stateSplitsAs s s2 s1.
Proof. move => H f. by apply: splitsAs_commutative. Qed.

Lemma stateSplitsAs_associative s s1 s2 s3 s4 :
  stateSplitsAs s s1 s2 ->
  stateSplitsAs s2 s3 s4 ->
  exists s5,
  stateSplitsAs s s3 s5 /\
  stateSplitsAs s5 s1 s4.
Proof. move => H1 H2.
set s5 := fun fr => fun x => if s4 fr x is Some y then Some y else s1 fr x.
exists s5.
split; move => fr; apply (splitsAs_associative (H1 fr) (H2 fr)).
Qed.

Definition restrictState (s: PState) (p: forall f:Frag, fragDom f -> bool) : PState :=
  fun f => fun x => if p f x then s f x else None.

Lemma stateSplitsOn (s: PState) p :
stateSplitsAs s (restrictState s p)
                (restrictState s (fun f => fun x => ~~p f x)).
Proof. move => f x.
case E: (s f x) => [a |] => //. rewrite /restrictState.
case E': (p f x). rewrite E. left; done. right. by rewrite E.
rewrite /restrictState.  rewrite E.
by case (p f x).
Qed.

(* Builds a total memory with the same mappings as the partial memory s.
   Locations that are not in s will be unmapped in the result. *)
Definition memComplete (s: PState) : Mem :=
  pmap_of (fun p =>
    match s Memory p with
    | Some (Some v) => Some v
    | _ => None
    end).

Lemma memComplete_inverse (s: PState) p v:
  s Memory p = Some v -> (memComplete s) p = v.
Proof.
  move=> Hsp. rewrite /memComplete. rewrite pmap_of_lookup.
  rewrite Hsp. by destruct v.
Qed.


(*---------------------------------------------------------------------------
    State predicates, and logical connectives
    We start without restrictions on predicates, roughly the "assertions" of
    Reynolds' "Introduction to Separation Logic", 2009.
  ---------------------------------------------------------------------------*)

Instance PStateEquiv : Equiv PState := {
   equiv s1 s2 := forall f, s1 f =1 s2 f
}.

Instance PStateType : type PState.
Proof.
  split.
  move => s f x; reflexivity.
  move => s1 s2 Hs f x; specialize (Hs f x); symmetry; assumption.
  move => s1 s2 s3 H12 H23 f x; specialize (H12 f x); specialize (H23 f x).
  transitivity (s2 f x); assumption.
Qed.

Instance addRegPieceToPStateEquiv_m :
  Proper (equiv ==> eq ==> eq ==> equiv) addRegPieceToPState.
Proof.
  move => p q Hpeq r1 r2 Hr1eqr2 w1 w2 Hw1eqw2 f x; subst.
  destruct f; simpl; rewrite Hpeq; reflexivity.
Qed.

Instance addFlagToPStateEquiv_m :
  Proper (equiv ==> eq ==> eq ==> equiv) addFlagToPState.
Proof.
  move => p q Hpeq r1 r2 Hr1eqr2 w1 w2 Hw1eqw2 f x; subst.
  destruct f; simpl; rewrite Hpeq; reflexivity.
Qed.

Instance addBYTEToPStateEquiv_m :
  Proper (equiv ==> eq ==> eq ==> equiv) addBYTEToPState.
Proof.
  move => p q Hpeq r1 r2 Hr1eqr2 w1 w2 Hw1eqw2 f x; subst.
  destruct f; simpl; rewrite Hpeq; reflexivity.
Qed.

Instance extendStateEquiv_m :
  Proper (equiv ==> equiv ==> equiv) extendState.
Proof.
  move => p q Hpeqq r1 r2 Hr1eqr2 f d.
  unfold extendState, extend.
  rewrite Hr1eqr2. destruct (r2 f d); [|rewrite Hpeqq]; reflexivity.
Qed.

Instance stateIncludeInEquiv_m :
  Proper (equiv ==> equiv ==> iff) stateIncludedIn.
Proof.
  move => p q Hpeqq r1 r2 Hr1eqr2.
  split; move => H f d y Heq; specialize (H f d y);
  [rewrite <- Hpeqq in Heq | rewrite Hpeqq in Heq];
  specialize (H Heq); [rewrite <- Hr1eqr2| rewrite Hr1eqr2];
  assumption.
Qed.

Lemma state_extensional (s1 s2: PState) : (forall f, s1 f =1 s2 f) -> s1 === s2.
Proof. unfold equiv, PStateEquiv; move => H f; apply H. Qed.

Program Definition my_sa_mul : (PState -s> PState -s> PState -s> Prop) :=
  lift3s (fun s1 s2 s => forall f, splitsAs (s f) (s1 f) (s2 f)) _ _ _.
Next Obligation.
  intros t1 t2 HEqt; unfold equiv, PStateEquiv in HEqt.
  split; intros; [rewrite <- HEqt | rewrite HEqt]; apply H.
Qed.
Next Obligation.
  intros t1 t2 HEqt; unfold equiv, PStateEquiv in HEqt;
  split; simpl; intros; [rewrite <- HEqt | rewrite HEqt]; apply H.
Qed.
Next Obligation.
  intros t1 t2 HEqt; unfold equiv, PStateEquiv in HEqt.
  split; simpl; intros; [rewrite <- HEqt | rewrite HEqt]; apply H.
Qed.

Instance PStateSepAlgOps: SepAlgOps PState := {
  sa_unit := emptyPState;
  sa_mul s1 s2 s := stateSplitsAs s s1 s2
}.

Instance PStateSepAlg : SepAlg PState.
Proof.
  split.
  + move => a b c d Habc Hceqd f; specialize (Hceqd f); rewrite <- Hceqd.
    apply Habc.
  + move => a b c d Habc Habd f.
    eapply splitsAs_functional; [apply Habc | apply Habd].
  + move => a b c Hbc d. split.
    - move => Habd f; specialize (Hbc f); rewrite <- Hbc; apply Habd.
    - move => Hacd f; specialize (Hbc f); rewrite Hbc; apply Hacd.
  + split; intros; by apply stateSplitsAs_commutative.
  + move => a b c bc abc H1 H2. eapply stateSplitsAs_associative. apply H1. apply H2.
  + intros; apply stateSplitsAs_s_s_emp.
Qed.

Definition SPred := ILFunFrm PState Prop.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.
Local Existing Instance SABIOps.
Local Existing Instance SABILogic.

(* Giving these cost 1 ensures that they are preferred over spec/Prop instances *)
Instance sepILogicOps : ILogicOps SPred | 1 := _.
Instance sepLogicOps : BILOperators SPred | 1 := _.
Instance sepLogic : BILogic SPred | 1 := _.
Global Opaque sepILogicOps sepLogicOps sepLogic.

Implicit Arguments mkILFunFrm [[e] [ILOps]].

Definition mkSPred (P : PState -> Prop)
        (f : forall t t' : PState, t === t' -> P t |-- P t') : SPred :=
  mkILFunFrm PState Prop P f.

Implicit Arguments mkSPred [].

Local Transparent lentails sepILogicOps.
Program Definition eq_pred s := mkSPred (fun s' => s === s') _.
Next Obligation.
  rewrite <- H; assumption.
Qed.

Local Transparent ILFun_Ops.
Instance eq_pred_equiv_lentails :
  Proper (equiv ==> lentails) eq_pred.
Proof.
  move => s t Hseqt u Hsequ; simpl in *.
  rewrite <- Hseqt. assumption.
Qed.

Instance eq_pred_equiv_lequiv :
  Proper (equiv ==> lequiv) eq_pred.
Proof.
  split; apply eq_pred_equiv_lentails; [|symmetry]; assumption.
Qed.

Instance eq_pred_eq_pred_lentails :
  Proper (eq_pred ==> lentails) eq_pred.
Proof.
  move => s t Hseqt u Hsequ; simpl in *.
  rewrite <- Hseqt. assumption.
Qed.

Instance eq_pred_eq_pred_lequiv :
  Proper (eq_pred ==> lequiv) eq_pred.
Proof.
  split; apply eq_pred_equiv_lentails; [|symmetry]; assumption.
Qed.

Lemma lentails_eq (P : SPred) t :
  P t <-> eq_pred t |-- P.
Proof.
  split.
  - simpl. intros H x H1.
    assert (P t |-- P x) as H2 by (eapply ILFunFrm_closed; assumption).
    apply H2; assumption.
  - simpl; intros; firstorder.
Qed.


(* Need lemma about splitting involving a total (e.g. toPState) "partial" store.
   e.g. sa_mul (toPState s) s0 s1 -> s1 = s /\ s0 = emptyPState *)
Definition isTotal T U (f: T -> option U) := forall x, f x <> None.
Definition isTotalPState (s: PState) := forall f:Frag, isTotal (s f).

Lemma splitsTotal T U (s s0 s1: T -> option U) : isTotal s0 -> splitsAs s s0 s1 -> s =1 s0.
Proof. move => TOT SPLITS. rewrite /splitsAs in SPLITS.
move => x. unfold isTotal in TOT.
specialize (SPLITS x). specialize (TOT x).
destruct (s0 x) => //. destruct (s x) => //.
elim SPLITS => [[H1 H2] | [H1 H2]]. done. done. by destruct SPLITS.
Qed.

Lemma stateSplitsTotal (s s0 s1: PState) : isTotalPState s0 -> stateSplitsAs s s0 s1 -> s === s0.
Proof. move => TOT SPLITS. unfold stateSplitsAs in SPLITS. unfold isTotalPState in TOT.
move => f. apply: splitsTotal => //. Qed.

Instance stateSplitsAs_m :
  Proper (csetoid.equiv ==> csetoid.equiv ==> csetoid.equiv ==> iff) stateSplitsAs.
Proof. move => s1 s2 EQ s1' s2' EQ' s1'' s2'' EQ''.
split => SPLIT f x.
specialize (SPLIT f x). specialize (EQ f x). specialize (EQ' f x). specialize (EQ'' f x).
destruct (s1 f x); destruct (s2 f x); congruence.
specialize (SPLIT f x). specialize (EQ f x). specialize (EQ' f x). specialize (EQ'' f x).
destruct (s1 f x); destruct (s2 f x); congruence.
Qed.

Local Transparent ILFun_Ops SABIOps ltrue.

Lemma emp_unit : empSP -|- eq_pred sa_unit.
  split; simpl; move => x H.
  + destruct H as [H _]; assumption.
  + exists H; constructor.
Qed.

Lemma eqPredTotal_sepSP_trueR s :
  isTotalPState s ->
  eq_pred s -|- eq_pred s ** ltrue.
Proof.
move => TOT.
split => s'.
- apply lentails_eq. exists s, emptyPState. split => //; first apply stateSplitsAs_s_s_emp.
- move => /= [s1 [s2 [H1 [H2 H3]]]]. hnf in H2, H1. setoid_rewrite <- H2 in H1.
  apply (stateSplitsTotal TOT) in H1. by rewrite H1.
Qed.

Lemma eqPredTotal_sepSP s1 s2 R:
  isTotalPState s2 ->
  eq_pred s1 |-- eq_pred s2 ** R ->
  empSP |-- R.
Proof. move => TOT H.
apply lentails_eq in H. destruct H as [s3 [s4 [H1 [H2 H3]]]].
simpl in H2. rewrite <-H2 in H1.
simpl in H1.
rewrite -> (stateSplitsTotal TOT H1) in H1.
apply stateSplitsAs_s_s_t in H1.
subst. rewrite emp_unit. by apply lentails_eq.
Qed.

Local Opaque SABIOps.

Global Coercion lbool (b:bool) := lpropand b ltrue.

(*===========================================================================
    "is" predicates on registers and flags
  ===========================================================================*)

Definition regPieceIs r v : SPred := eq_pred (addRegPieceToPState emptyPState r v).
Definition flagIs f b : SPred := eq_pred (addFlagToPState emptyPState f b).
(*Definition BYTEregIs (r:Reg OpSize1) v : SPred := regPieceIs (BYTERegToRegPiece r) v.*)

Definition reg64Is (r:Reg64) (v:QWORD) : SPred :=
  let pi i := regPieceIs (mkRegPiece r i) (getRegPiece v i) in
   pi 0 ** pi 1 ** pi 2 ** pi 3 ** pi 4 ** pi 5 ** pi 6 ** pi 7.

Definition reg32Is (r:Reg32) (v:DWORD) : SPred :=
  let pi i := regPieceIs (mkRegPiece (Reg32_base r) i) (getRegPiece v i) in
   pi 0 ** pi 1 ** pi 2 ** pi 3.

Definition reg16Is (r:Reg16) (v:WORD) : SPred :=
   regPieceIs (mkRegPiece (Reg16_base r) 0) (slice 0 8 8 v)
** regPieceIs (mkRegPiece (Reg16_base r) 1) (slice 8 8 0 v).

Definition reg8Is (r:Reg8) (v:BYTE) : SPred :=
   regPieceIs (mkRegPiece (Reg8_base r) 0) v.

Inductive RegOrFlag :=
| RegOrFlagR s :> Reg s -> RegOrFlag
| RegOrFlagF :> Flag -> RegOrFlag.

Definition RegOrFlag_target rf :=
match rf with
| RegOrFlagR s _   => VWORD s
| RegOrFlagF _     => FlagVal
end.

Definition stateIs (x: RegOrFlag) : RegOrFlag_target x -> SPred :=
match x with
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

(*---------------------------------------------------------------------------
     Byte-is predicate
  ---------------------------------------------------------------------------*)
Program Definition byteIs p b : SPred := eq_pred (addBYTEToPState emptyPState p b).

Definition byteAny p : SPred := lexists (byteIs p).

Instance flagIsEquiv_m :
  Proper (eq ==> eq ==> csetoid.equiv ==> iff) flagIs.
Proof.
  intros n m Hneqm f g Hbeqc p q Hpeqq; subst.
  split; simpl; rewrite <- Hpeqq; tauto.
Qed.

Instance byteIsEquiv_m :
  Proper (eq ==> eq ==> csetoid.equiv ==> iff) byteIs.
Proof.
  intros n m Hneqm b c Hbeqc p q Hpeqq; subst.
  split; simpl; rewrite <- Hpeqq; tauto.
Qed.

(*---------------------------------------------------------------------------
    Iterated separating conjunction
  ---------------------------------------------------------------------------*)
Fixpoint isc {A} (I: seq A) (F: A -> SPred) :=
  match I with
  | nil => empSP
  | i :: I' => F i ** isc I' F
  end.

Lemma isc_cat {A} (I J: seq A) F :
  isc (I ++ J) F -|- isc I F ** isc J F.
Proof.
  elim: I.
  - simpl; rewrite sepSPC. rewrite empSPR. reflexivity.
  - move=> i I IH /=. by rewrite IH sepSPA.
Qed.

Lemma isc_snoc {A} (I: seq A) i F :
  isc (I ++ [:: i]) F -|- isc I F ** F i.
Proof. rewrite isc_cat /=. by rewrite empSPR. Qed.

(*---------------------------------------------------------------------------
    Strictly exact assertions

    See Section 2.3.2 In Reynolds's "Introduction to Separation Logic" online
    lecture notes.
    http://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/cs818A3-11.html
  ---------------------------------------------------------------------------*)

Class StrictlyExact (P: SPred) := strictly_exact:
  forall s s', P s -> P s' -> s === s'.

Instance StrictlyExactRegPieceIs r v: StrictlyExact (regPieceIs r v).
Proof. move => s s'. simpl. by move ->. Qed.

Instance StrictlyExactFlagIs f v: StrictlyExact (flagIs f v).
Proof. move => s s'. simpl. by move ->. Qed.

Instance StrictlyExactByteIs p v: StrictlyExact (byteIs p v).
Proof. move => s s'. simpl. by move ->. Qed.

Instance StrictlyExactSep P Q `{PH: StrictlyExact P} `{QH: StrictlyExact Q}
  : StrictlyExact (P**Q).
Proof. move => s s' [s1 [s2 [H1 [H2 H3]]]] [s1' [s2' [H1' [H2' H3']]]].
specialize (PH s1 s1' H2 H2').
specialize (QH s2 s2' H3 H3').
rewrite -> PH, QH in H1.
by rewrite (stateSplitsAsExtends H1) (stateSplitsAsExtends H1').
Qed.

Instance StrictlyExactRegIs r v: StrictlyExact (reg64Is r v).
Proof. rewrite /reg64Is. do 7 (apply StrictlyExactSep; first apply StrictlyExactRegPieceIs).
apply StrictlyExactRegPieceIs. Qed.

Instance StrictlyExactEmpSP : StrictlyExact empSP.
Proof. move => s s' H H'.
destruct H as [H _]. destruct H' as [H' _].
by rewrite -H -H'.
Qed.

Instance StrictlyExactConj P Q `{PH: StrictlyExact P} `{QH: StrictlyExact Q}
  : StrictlyExact (P //\\ Q).
Proof. move => s s' [H1 H2] [H1' H2'].
by apply (PH s s' H1 H1').
Qed.

Class Precise (P: SPred) := precise:
  forall s s1 s2, stateIncludedIn s1 s -> stateIncludedIn s2 s -> P s1 -> P s2 -> s1 === s2.

Instance PreciseStrictlyExact P `{PH: StrictlyExact P} : Precise P.
Proof. move => s s1 s2 H1 H2. intuition. Qed.

Corollary Distributive P0 P1 Q `{QH: Precise Q} :
  (P0 ** Q) //\\ (P1 ** Q) |-- (P0 //\\ P1) ** Q.
Proof.
unfold "|--". rewrite /sepILogicOps/ILFun_Ops. move => s [H0 H1].
destruct H0 as [s0 [s0' [H0a [H0b H0c]]]].
destruct H1 as [s1 [s1' [H1a [H1b H1c]]]].
have SSI0 := stateSplitsAsIncludes H0a.
have SSI1 := stateSplitsAsIncludes H1a.
destruct SSI0 as [SSI0a SSI0b].
destruct SSI1 as [SSI1a SSI1b].
have QH1 := (QH _ _ _ SSI0b SSI1b H0c H1c).
exists s0. exists s1'.
split. rewrite -> QH1 in H0a.

exact H0a.
split. split. exact H0b. rewrite -> QH1 in SSI0b.
rewrite -> QH1 in H0a.
rewrite <- (stateSplitsAs_functionalArg H1a H0a). exact H1b.
exact H1c.
Qed.

(*---------------------------------------------------------------------------
    A partial application of [eq] is a predicate
  ---------------------------------------------------------------------------*)

Lemma stateSplitsAs_eq s s1 s2:
  sa_mul s1 s2 s ->
  eq_pred s1 ** eq_pred s2 -|- eq_pred s.
Proof.
  split.
  - move=> s' [s1' [s2' [Hs' [Hs1' Hs2']]]].
    Opaque sa_mul.
    simpl in *.
    rewrite <- Hs1', <- Hs2' in Hs'.
    eapply sa_mul_eqR; eassumption.
  - simpl. move=> s' H1.
    rewrite -> H1 in H.
    exists s1; exists s2; done.
Qed.

Lemma ILFun_exists_eq (P : SPred) :
  P -|- Exists s, P s /\\ eq_pred s.
Proof.
  split; intros s Hs.
  - exists s. constructor; simpl; intuition.
  - simpl in *; destruct Hs as [x [Hp Hs]].
    assert (P x |-- P s) as H by (eapply ILFunFrm_closed; assumption).
    by apply H.
Qed.

Global Opaque PStateSepAlgOps.

(*---------------------------------------------------------------------------
    Some lemmas about the domains of primitive points-to-like predicates
  ---------------------------------------------------------------------------*)
Open Scope spred_scope.

Lemma regPieceIs_same (r:RegPiece) v1 v2 : regPieceIs r v1 ** regPieceIs r v2 |-- lfalse.
Proof.  move => s [s1 [s2 [H1 [H1a H1b]]]].
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

(*
Lemma regIs_same s (r:VRegAny s) (v1 v2:VWORD s) : r ~= v1 ** r ~= v2 |-- lfalse.
Proof. destruct s. 
- apply regPieceIs_same. 
- destruct r. admit. 
- rewrite /stateIs/regIs. 
  rewrite sepRev4. rewrite sepSPA.
  rewrite sepRev4. rewrite -!sepSPA. rewrite -> (@regPieceIs_same (AnyRegPiece r (inord 0))).
  by rewrite !sepSP_falseL. 
Qed.
*)

Lemma flagIs_same (f:Flag) v1 v2 : f ~= v1 ** f ~= v2 |-- lfalse.
Proof.  move => s [s1 [s2 [H1 [H1a H1b]]]].
simpl in H1a, H1b. rewrite <-H1a in H1. rewrite <-H1b in H1.
rewrite /sa_mul/PStateSepAlgOps/= in H1.
specialize (H1 Flags f). simpl in H1.
destruct (s Flags f); rewrite eq_refl in H1.
destruct H1; by destruct H.
by destruct H1.
Qed.

Lemma byteIs_same p v1 v2 : byteIs p v1 ** byteIs p v2 |-- lfalse.
Proof.  move => s [s1 [s2 [H1 [H1a H1b]]]].
simpl in H1a, H1b. rewrite <-H1a in H1. rewrite <-H1b in H1.
rewrite /sa_mul/PStateSepAlgOps/= in H1.
specialize (H1 Memory p). simpl in H1.
destruct (s Memory p); rewrite eq_refl in H1.
destruct H1; by destruct H.
by destruct H1.
Qed.

(* We don't want simpl to unfold this *)
Global Opaque stateIs.

