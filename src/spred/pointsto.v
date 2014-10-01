(*===========================================================================
    Points-to predicates
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq Ssreflect.choice Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops x86proved.x86.procstate x86proved.x86.addr.
Require Import x86proved.monad x86proved.reader x86proved.writer x86proved.roundtrip x86proved.spred.core x86proved.spred.stateis x86proved.spred.tactics x86proved.pfun x86proved.cursor x86proved.charge.iltac x86proved.charge.ilogic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
   The intended meaning of
      p -- q :-> v
   is that the memory from p inclusive to q exclusive represents the value v.

   Points-to is a derived notion:
      p :-> v
   iff there exists some q such that p -- q :-> v.

   We require that memIs p q v implies p<=q.
  ---------------------------------------------------------------------------*)
Class MemIs T := {
  memIs:> ADDRCursor -> ADDRCursor -> T -> SPred;
  memIsLe :> forall p q v, memIs p q v |-- leCursor p q /\\ memIs p q v
}.

Notation "p '--' q ':->' x" := (memIs p q x) (at level 50, q at next level, no associativity).

Definition pointsTo {R} {_:MemIs R} p v := Exists q, memIs p q v.
Notation "p :-> ? : t" := (Exists x:t, pointsTo p x)(at level 50, no associativity).
Notation "p :-> x" := (pointsTo p x) (at level 50, no associativity).

(* Trivial consequence *)
Lemma memIs_pointsTo {R} {_:MemIs R} p q v :
  p -- q :-> v |-- p :-> v.
Proof. rewrite /pointsTo. by apply lexistsR with q. Qed.

(* This is a consequence of memIsLe *)
Lemma memIsNonTop T {_:MemIs T} (v: T) (p: ADDRCursor) (q:ADDR) :
    p -- q :-> v |-- Exists p':ADDR, p = mkCursor p' /\\ p -- q :-> v.
Proof. eapply lentailsPre. apply memIsLe.
sdestruct => H. elim (leCursorNonTop H) => [p' EQ].
apply lexistsR with p'. rewrite EQ. sbazooka.
Qed.

(* This is another consequence of memIsLe *)
(* We leave the argument to [top] unspecified so that it may be picked up as a constant an not be a numeral. *)
Lemma memIsFromTop T (_:MemIs T) (v: T) (q: ADDR) :
  top _ -- q :-> v |-- lfalse.
Proof. rewrite -> memIsLe. rewrite /leCursor. by apply lpropandL. Qed.

(* Our characterisation of fixed-size encodings *)
Class FixedMemIs T n `(MI: MemIs T) :=
  memIsFixed:> forall p q v, p -- q :-> v |-- apart n p q /\\ p -- q :-> v.

(* This isn't true for n = 2^32 *)
Lemma fixedMemIs_pointsTo X `{_:FixedMemIs X} (p:ADDR) v :
  n<2^naddrBits -> leB p (p+#n) -> p :-> v |-- p -- (p+#n) :-> v.
Proof. move => LT LE.
rewrite /pointsTo. sdestruct => q. 
rewrite -> memIsFixed. sdestruct => AP.
rewrite (leB_apart LT LE AP).  reflexivity. 
Qed.

Tactic Notation "not" tactic1(t) := try (t; fail 1).

  Ltac cheap_unify p :=
    match p with
    | (?a,?b) => is_evar a; first [unify a b | fail 1]
    | (?a,?b) => is_evar b; first [unify a b | fail 1]
    | (?a,?b) => not (has_evar a); not (has_evar b); first [constr_eq a b | fail 1]
    | (?fa ?xa,?fb ?xb) => cheap_unify (fa, fb); cheap_unify (xa, xb)
    end.

Ltac unifyPT P :=
  match P with
    (* These are surely safe *)
  | (byteIs ?p ?v, byteIs ?p ?w) => unify v w
  | (?p :-> ?v, ?p :-> ?w) => unify v w
  | (?i -- ?j :-> ?v, ?i -- ?k :-> ?v) => unify j k
    (* These might be overlapping ranges, but typically we don't expect to see this *)
  | (?i -- ?j :-> ?v, ?i -- ?k :-> ?w) => (unify j k; unify v w)
    (* This seems risky. There might be multiple ranges pointing to the same value *)
  | (?i -- ?j :-> ?v, ?k -- ?l :-> ?v) => (unify i k; unify j l)

  | (stateIs (@RegOrFlagR ?s ?r) ?v, stateIs (@RegOrFlagR ?s ?t) ?w) => 
    (not (has_evar r); not (has_evar t); (unify r t; cheap_unify (v,w)))
  | (stateIs (@RegOrFlagF ?r) ?v, stateIs (@RegOrFlagF ?t) ?w) => 
    (not (has_evar r); not (has_evar t); (unify r t; cheap_unify (v,w)))
  | (stateIs ?r ?v, stateIs ?r ?w) => Solving.cheap_unify (v, w)
  | (?s ?v,?s ?w) => cheap_unify (v, w)
  | _ => Solving.cheap_unify P
  end.

Ltac ssimpl := ssimpl_with unifyPT.
Ltac sbazooka := sbazooka_with unifyPT.


(*---------------------------------------------------------------------------
   We can interpret reader terms purely logically, using the primitive
   byteIs predicate and separating conjunction.
  ---------------------------------------------------------------------------*)
Fixpoint interpReader T (rt:Reader T) (p q: ADDRCursor) (v: T) :=
  match rt with
  | readerRetn x =>
    v = x /\\ p = q /\\ empSP

  | readerNext rd =>
    (* We can't read beyond the last byte of memory! *)
    if p is mkCursor p'
    then Exists b, byteIs p' b ** interpReader (rd b) (next p') q v
    else lfalse

  | readerSkip rd =>
    if p is mkCursor p'
    then Exists b, byteIs p' b ** interpReader rd (next p') q v
    else lfalse

  | readerCursor rd =>
    interpReader (rd p) p q v
  end.

Lemma interpReader_entails_leCursor T (rt: Reader T) :
  forall p q v, interpReader rt p q v |-- leCursor p q /\\ interpReader rt p q v.
Proof. elim rt; rewrite /interpReader-/interpReader.
- move => v p q w. sdestructs => -> ->. rewrite leCursor_refl. sbazooka.
- move => rd IH p q w. elim p => //. move => d. sdestructs => byte.
  rewrite -> IH. rewrite leCursor_next. sdestructs => LT. rewrite (leCursor_weaken LT).
  sbazooka.
- move => rd IH p q w. elim p => //. move => d. sdestructs => byte.
  rewrite -> IH. rewrite leCursor_next. sdestructs => LT. rewrite (leCursor_weaken LT).
  sbazooka.
- move => rd IH p q v. apply IH.
Qed.

Lemma interpReader_retn T (v w:T) p q:
  interpReader (retn v) p q w -|- p = q /\\ v = w /\\ empSP.
Proof. simpl (retn _). rewrite /interpReader-/interpReader.
sbazooka.
Qed.

Lemma interpReader_bind T1 T2 (r1: Reader T1) : forall (r2: T1 -> Reader T2) w p q,
  interpReader (readerBind r1 r2) p q w -|-
  Exists p', Exists v, interpReader r1 p p' v ** interpReader (r2 v) p' q w.
Proof. induction r1 => r2 w p q.
+ rewrite /readerBind/interpReader-/interpReader. split.
  * sbazooka.
  * sdestructs => ? ? -> ->. sbazooka.
+ simpl readerBind. rewrite /interpReader-/interpReader.
  destruct p.
  * split.
      sdestructs => byte. rewrite H. sbazooka.
      sdestructs => p' v byte. setoid_rewrite H. sbazooka.
  * sbazooka.
(* readerSkip *)
+ simpl readerBind. rewrite /interpReader-/interpReader.
  destruct p.
  * split.
      sdestructs => byte. rewrite IHr1. sbazooka.
      sdestructs => p' v byte. setoid_rewrite IHr1. sbazooka.
  * sbazooka.
(* readerCursor *)
  rewrite /readerBind-/readerBind/interpReader-/interpReader.
  destruct p => //.
Qed.

Lemma interpReader_letPair T X Y (v:X*Y) (r: X -> Y -> Reader T) :
  interpReader (let (x,y) := v in r x y) = interpReader (r v.1 v.2).
Proof. by elim v. Qed.

(*---------------------------------------------------------------------------
  Typically we use interpReader to instantiate MemIs
  ---------------------------------------------------------------------------*)
Instance readerMemIs R {r:Reader R} : MemIs R :=
  @Build_MemIs _ (interpReader readNext) (@interpReader_entails_leCursor R r).

Lemma interpReaderPair T1 T2 (r1: Reader T1) (r2: Reader T2) v1 v2 p r :
  Exists q, interpReader r1 p q v1 ** interpReader r2 q r v2 -|-
  interpReader (let! x1 = r1; let! x2 = r2; retn (x1, x2)) p r (v1,v2).
Proof. rewrite interpReader_bind.
split.
+ sdestructs => q. sbazooka. sbazooka. rewrite interpReader_bind. sbazooka.
  simpl. sbazooka.
+ sdestructs => p' v. rewrite interpReader_bind. sdestructs => p'' v'.
  rewrite interpReader_retn. sdestructs => -> [-> ->]. sbazooka.
Qed.

Lemma readerMemIsSimpl R {r: Reader R} p q (v: R) :
  p -- q :-> v -|- interpReader r p q v.
Proof. by rewrite /memIs/=/readNext. Qed.

Definition fixedSizeReader R (r: Reader R) n :=
  forall p q v, interpReader r p q v |-- apart n p q /\\ interpReader r p q v.

(*---------------------------------------------------------------------------
   readerMemIs for bytes
  ---------------------------------------------------------------------------*)

Lemma interpReader_bindBYTE T (r: BYTE -> Reader T) w (p:ADDR) (q:ADDRCursor) :
  interpReader (readerBind readNext r) p q w -|-
  Exists b:BYTE, byteIs p b ** interpReader (r b) (next p) q w.
Proof. rewrite interpReader_bind/readNext/readBYTE/interpReader-/interpReader.
split. sbazooka. sbazooka. subst. by ssimpl. sbazooka.
Qed.

Lemma interpReader_bindBYTE_top T (r: BYTE -> Reader T) w (q:ADDRCursor) :
  interpReader (readerBind readNext r) (top _) q w -|-
  lfalse.
Proof.
rewrite interpReader_bind/readNext/readBYTE/interpReader-/interpReader.
sbazooka.
Qed.

Lemma fixedSizeBYTE : fixedSizeReader readBYTE 1.
Proof.
  rewrite /fixedSizeReader. move => p q b.
  destruct p; simpl.
  + sdestructs => b0 -> H1. sbazooka.
  + sbazooka.
Qed.


Instance FixedMemIsBYTE : FixedMemIs 1 (readerMemIs BYTE).
Proof. apply fixedSizeBYTE. Qed.

Lemma memIsBYTE_next_entails (p:ADDR) q (v:BYTE) :
  p -- q :-> v |-- q = next p /\\ p -- q :-> v.
Proof. have MI := @memIsFixed _ _ _ FixedMemIsBYTE p q v.
by simpl (apart _ _ _) in MI.
Qed.

(* In fact p :-> b for b:BYTE is just a long-winded way of saying byteIs p b *)
Lemma pointsToBYTE_byteIs (p:ADDR) b : p :-> b -|- byteIs p b.
Proof.
rewrite /pointsTo. split.
sdestruct => q. rewrite readerMemIsSimpl interpReader_bindBYTE.
rewrite /interpReader. sdestructs => b' -> _. by ssimpl.
apply lexistsR with (next p).
rewrite readerMemIsSimpl interpReader_bindBYTE.
sbazooka. rewrite interpReader_retn. sbazooka.
Qed.

(*---------------------------------------------------------------------------
   MemIs for unit type, pairs and sequences
  ---------------------------------------------------------------------------*)

Definition unitMemIs (p q: ADDRCursor) (v: unit) := p = q /\\ empSP.

Lemma unitMemIsLe p q v : unitMemIs p q v |-- leCursor p q /\\ unitMemIs p q v.
Proof. rewrite /unitMemIs. sdestruct => ->. rewrite leCursor_refl. sbazooka. Qed.

Global Instance UnitMemIs : MemIs unit := Build_MemIs unitMemIsLe.

Section PairMemIs.

  Context {X Y} {MX: MemIs X} {MY: MemIs Y}.

  Definition pairMemIs :=
    fun p q (v: X*Y) => Exists p', p -- p' :-> (fst v) ** p' -- q :-> (snd v).

  Lemma pairMemIsLe p q v : pairMemIs p q v |-- leCursor p q /\\ pairMemIs p q v.
  Proof. rewrite /pairMemIs. sdestruct => p'. destruct v as [x y]. rewrite /fst/snd.
  rewrite -> memIsLe. sdestruct => LE1. rewrite -> (@memIsLe _ _ p'). sdestruct => LE2.
  rewrite (leCursor_trans LE1 LE2). sbazooka.
  Qed.

  Global Instance PairMemIs : MemIs (X*Y) := Build_MemIs pairMemIsLe.

  Lemma pairMemIsSimpl p q (v : X*Y) :
    p -- q :-> v -|- Exists p', p -- p' :-> v.1 ** p' -- q :-> v.2.
  Proof. by rewrite {1}/memIs/PairMemIs/pairMemIs. Qed.

  Lemma pairMemIsPair p q (x: X) (y: Y) :
    p -- q :-> (x,y) -|- Exists p', p -- p' :-> x ** p' -- q :-> y.
  Proof. apply pairMemIsSimpl. Qed.

  Lemma pairMemIsPair' (p q: ADDR) (x: X) (y: Y) :
    p -- q :-> (x,y) -|- Exists p':ADDR, p -- p' :-> x ** p' -- q :-> y.
  Proof. rewrite pairMemIsPair. 
  split; sdestruct => p'. 
  - destruct p'. sbazooka. rewrite -> memIsFromTop. sbazooka. 
  - apply lexistsR with p'. sbazooka.
  Qed.


(*
  Context (dx dy: DWORD) {FX: FixedMemIs dx MX} {FY: FixedMemIs dy MY}.
  Instance FixedMemIsPair : FixedMemIs (addB dx dy) PairMemIs.
  Proof. move => p q [x y].
  rewrite pairMemIsPair. sdestruct => p'.
  rewrite -> (@memIsFixed _ dx _ _ p).
  rewrite -> (@memIsFixed _ dy _ _ p').
  sdestructs => Dx Dy.
  rewrite -> (@memIsLe _ _ p).
  rewrite -> (@memIsLe _ _ p').
  sdestructs => Lx Ly.
  rewrite (cursorSub_addB Lx Ly Dx Dy). sbazooka.
  Qed.
*)

End PairMemIs.

Section SeqMemIs.

  Context {X} {MX: MemIs X}.

  Definition optionMemIs p q (v: option X) :=
    match v with
    | Some v => p -- q :-> v
    | None => p = q /\\ empSP
  end.

  Lemma optionMemIsLe p q v : optionMemIs p q v |-- leCursor p q /\\ optionMemIs p q v.
  Proof. elim v.
  + move => x. apply memIsLe.
  + simpl. sdestruct => ->. sbazooka. by rewrite leCursor_refl.
  Qed.

  Global Instance OptionMemIs : MemIs (option X) := Build_MemIs optionMemIsLe.

  Fixpoint seqMemIs p q (vs: seq X) :=
    match vs with
    | v::vs => Exists p', p -- p' :-> v ** seqMemIs p' q vs
    | nil => p = q /\\ empSP
    end.

  Lemma seqMemIsLeAux vs : forall p q, seqMemIs p q vs |-- leCursor p q /\\ seqMemIs p q vs.
  Proof. elim vs.
  + move => p q. rewrite /seqMemIs. sdestruct => ->. rewrite leCursor_refl. sbazooka.
  + move => x xs IH p q. rewrite /seqMemIs-/seqMemIs.
    sdestruct => p'. rewrite -> IH. rewrite -> memIsLe. sdestructs => LE1 LE2.
    rewrite (leCursor_trans LE1 LE2). sbazooka.
  Qed.

  Definition seqMemIsLe p q vs := @seqMemIsLeAux vs p q.

  Global Instance SeqMemIs : MemIs (seq X) := Build_MemIs seqMemIsLe.

  Lemma seqMemIsSimpl (p q:ADDRCursor) (xs: seq X):
    p -- q :-> xs -|- if xs is x::xs then Exists p', p -- p' :-> x ** p' -- q :-> xs
                                       else p = q /\\ empSP.
  Proof. case xs.
  + by rewrite /memIs/SeqMemIs/seqMemIs.
  + move => x xs'. rewrite /memIs/SeqMemIs/seqMemIs-/seqMemIs. by rewrite /memIs/SeqMemIs.
  Qed.

  Lemma seqMemIsCons (p q:ADDRCursor) (x:X) (xs: seq X):
    p -- q :-> (x::xs) -|- Exists p', p -- p' :-> x ** p' -- q :-> xs.
  Proof. apply seqMemIsSimpl. Qed.


  Lemma seqMemIsCons' (p q:ADDR) (x:X) (xs: seq X):
    p -- q :-> (x::xs) -|- Exists p':ADDR, p -- p' :-> x ** p' -- q :-> xs.
  Proof. rewrite seqMemIsSimpl. split. sdestruct => p'. destruct p'. sbazooka.
  rewrite -> memIsFromTop. sbazooka. sbazooka. 
  Qed. 

  Context {n} {MY: FixedMemIs n MX}.

  Lemma seqFixedMemIsCons' (p q:ADDR) (x:X) (xs: seq X):
    p -- q :-> (x::xs) -|- p -- (p+#n) :-> x ** (p +#n) -- q :-> xs.
  Proof. rewrite seqMemIsCons. 
  split. 
  - sdestruct => p'. destruct p'. 
    + rewrite -> memIsFixed. sdestruct => AP. rewrite (apart_addBn AP). sbazooka.
    + rewrite -> memIsFromTop. sbazooka. 
  - sbazooka.
  Qed. 

  Lemma seqMemIsNil (p q:ADDRCursor):
    p -- q :-> (nil:seq X) -|- p = q /\\ empSP.
  Proof. apply seqMemIsSimpl. Qed.

  Lemma seqMemIsCat p q (xs ys : seq X):
    p -- q :-> (xs ++ ys) -|- p -- q :-> (xs, ys).
  Proof.
    elim: xs p => [|x xs IHxs] p.
    - rewrite pairMemIsSimpl/fst/snd cat0s. split. sbazooka. erewrite seqMemIsNil. sbazooka.
      sdestructs => p'. rewrite seqMemIsNil. sdestructs => ->. sbazooka.
    - simpl ((x::xs) ++ ys). split.
      + rewrite pairMemIsSimpl seqMemIsCons /fst/snd.
        setoid_rewrite IHxs. sdestruct => p'. rewrite pairMemIsSimpl /fst/snd.
        sdestruct => q'.
        apply lexistsR with q'. rewrite seqMemIsCons. ssimpl.
        apply lexistsR with p'. sbazooka.
      + rewrite pairMemIsSimpl /fst/snd. sdestruct => p'.
        rewrite seqMemIsCons. rewrite seqMemIsCons.
        setoid_rewrite IHxs. sdestruct => q'. apply lexistsR with q'.
        rewrite pairMemIsSimpl. rewrite /fst/snd. ssimpl.
        apply lexistsR with p'. sbazooka.
  Qed.

  Lemma seqPointsToNil (p:ADDRCursor) : p :-> ([::]: seq X) -|- empSP.
  Proof.
    rewrite /pointsTo. split.
    + sdestructs => q. rewrite -> seqMemIsNil. by sdestruct => _.
    + apply lexistsR with p. rewrite seqMemIsNil. sbazooka.
  Qed.

End SeqMemIs.


Lemma seqFixedMemIsConsNE X `(FMI:FixedMemIs X) (p q : ADDR) (v:X) vs : 0 < n < 2^naddrBits -> 
    p -- q :-> (v::vs) |-- p != q /\\ memIs p q (v::vs).
Proof. move/andP => [GT LT]. case E: n => [|n']; subst => //. 
  rewrite -> seqFixedMemIsCons'. 
  have H: p != p+#n'.+1. by apply: addBn_ne. 
  (* Why can't I identify the right memIs? *)
  rewrite -> memIsLe at 1. sdestruct => H1. 
  rewrite sepSPC. 
  rewrite -> memIsLe at 1. sdestruct => H2. 
  rewrite leCursor_nat in H1.
  rewrite leCursor_nat in H2.
  rewrite leq_eqVlt in H1. 
  have HI:= @cursorToNat_inj _ p (p+#n'.+1). 
  case E: (cursorToNat p == cursorToNat (p+#n'.+1)). 
  rewrite (eqP E) in HI. specialize (HI (refl_equal _)). injection HI => HI'. rewrite {1}HI' in H. 
  by rewrite eq_refl in H. rewrite E orFb in H1. 
  have NE: cursorToNat p != cursorToNat q. apply negbT. apply: ltn_eqF. by apply: leq_trans H2. 
  rewrite inj_eq in NE; last by apply cursorToNat_inj.
  rewrite NE.
  sbazooka.  
Qed. 

(*---------------------------------------------------------------------------
   MemIs for subtype
  ---------------------------------------------------------------------------*)

Section SubMemIs.

  Context {X} {MX : MemIs X}.

  Definition subMemIs P p q (v: {x:X | P x}) := p -- q :-> sval v.
  Implicit Arguments subMemIs [].

  Lemma subMemIsLe P p q v : subMemIs P p q v |-- leCursor p q /\\ subMemIs P p q v.
  Proof. rewrite /subMemIs. apply memIsLe. Qed.

  Global Instance SubMemIs P : MemIs {x : X | P x} := Build_MemIs (@subMemIsLe P).

  Lemma subMemIsSub P p q (v: {x:X | P x}) : p -- q :-> v |-- p -- q :-> sval v.
  Proof. by rewrite /=/subMemIs. Qed.

  Lemma seqSubMemIsMapAux P (vs: seq {x:X | P x}) : forall p q,
     p -- q :-> vs -|- p -- q :-> map sval vs.
  Proof. elim vs.
  + move => p q. rewrite !seqMemIsNil. sbazooka.
  + move => v vs' IH p q.
    rewrite !seqMemIsCons. split.
    - sdestruct => q'. apply lexistsR with q'. rewrite <- subMemIsSub.
      by rewrite -IH.
    - sdestruct => p'. rewrite -IH. apply lexistsR with p'. ssimpl. reflexivity.
  Qed.

  Lemma seqSubMemIs P p q (vs: seq {x:X | P x}) : p -- q :-> vs -|- p -- q :-> map sval vs.
  Proof. apply seqSubMemIsMapAux. Qed.

End SubMemIs.

Lemma memIs_consBYTE (p:ADDR) q (b:BYTE) bs : p -- q :-> (b::bs) -|- p :-> b ** (next p) -- q :-> bs.
Proof.
split.
  rewrite -> seqMemIsCons. sdestruct => q'.
  rewrite -> memIsBYTE_next_entails.
  sdestructs => ->. rewrite /pointsTo. sbazooka.

  rewrite /pointsTo. sdestructs => p'. rewrite -> memIsBYTE_next_entails.
  rewrite -> seqMemIsCons.
  sdestructs => ->. sbazooka.
Qed.

Lemma pointsToBYTE_NonTop (c : ADDRCursor) (b:BYTE) :
  c :-> b |-- Exists bits, c = mkCursor bits /\\ c :-> b.
Proof.
elim c => [bits |].
sbazooka.
rewrite {1}/pointsTo.
setoid_rewrite interpReader_bindBYTE_top.
by sdestructs => _.
Qed.

Lemma pointsTo_consBYTE (p:ADDR) (b:BYTE) bs : p :-> (b::bs) -|- p :-> b ** (next p) :-> bs.
Proof.
rewrite /pointsTo.
split.
  sdestruct => q. rewrite -> seqMemIsCons. sdestruct => q'.
  rewrite -> memIsBYTE_next_entails.
  sdestructs => ->. sbazooka.

  sdestructs => q q'.
  apply lexistsR with q'.
  rewrite -> seqMemIsCons. rewrite -> memIsBYTE_next_entails.
  sdestructs => ->. sbazooka.
Qed.


Lemma seq_BYTE_size (p q: ADDR) (vs: seq BYTE) :
  p -- q :-> vs |-- q = p +# size vs /\\ p -- q :-> vs.
Proof.
  elim: vs p => [|b bs IHbs] p.
  - rewrite -> seqMemIsNil. sdestruct => [[<-]]. ssplits => //.
    by rewrite addB0.
  - rewrite -> seqMemIsCons. rewrite /size -/size. sdestruct => [[p'|]].
    - rewrite ->IHbs. sdestruct => Hq. rewrite ->memIsBYTE_next_entails.
      sdestruct => Hp'. symmetry in Hp'. subst. ssplit; last by sbazooka.
      clear IHbs. replace (p +# (size bs).+1) with (incB p +# size bs).
      apply nextIsInc in Hp'. subst. rewrite <-addB_addn. rewrite -addB1.
      by rewrite ->addB_addn. rewrite -addB1. rewrite <-addB_addn. by rewrite add1n.
    - rewrite -> memIsFromTop.  rewrite lfalse_is_exists. sdestruct => [[]].
Qed.

Lemma seqMemIsBYTE_addn (vs:seq BYTE) : forall m (p:ADDR),
  m < 2^naddrBits ->
  p -- (p+#m) :-> vs |--
  size vs = m /\\ p -- (p+#m) :-> vs.
Proof.
  induction vs => m p BOUND.
(* vs is nil *)
  setoid_rewrite seqMemIsNil.
  sdestruct => EQ.
  have H: m = 0.
  apply (addB0_inv (p:=p) BOUND). have: p = p +# m by congruence. by move => {1}->.
  rewrite H addB0. sbazooka.
(* vs is non-nil *)
  setoid_rewrite seqMemIsCons.
  sdestruct => p'.
  rewrite -> memIsBYTE_next_entails.
  sdestruct => ->.

  destruct m as [|m].
    rewrite addB0. rewrite -> (@memIsLe _ _ (next p)). rewrite leCursor_next /ltCursor.
    rewrite ltB_nat ltnn.  rewrite lpropandF. by ssimpl.
    simpl (size _). apply ltnW in BOUND.
    specialize (IHvs m (p+#1) BOUND). rewrite <- addB_addn in IHvs. rewrite add1n in IHvs.

    case E: (next p) => [q |].
      symmetry in E. have NI := nextIsInc (sym_equal E). subst.
      rewrite -> IHvs. sbazooka.  congruence.
      rewrite -> memIsFromTop. by ssimpl.
Qed.


Lemma topPointsTo_consBYTE (x:BYTE) (xs: seq BYTE) : top _ :-> (x::xs) -|- lfalse.
Proof. split => //.
rewrite /pointsTo. sdestruct => q. rewrite -> seqMemIsCons. sdestruct => p'.
rewrite readerMemIsSimpl /readBYTE/=. sbazooka.
Qed.

Fixpoint catBYTES (xs: seq BYTE) : BITS (size xs * 8) :=
  if xs is x::xs return BITS (size xs * 8) then catBYTES xs ## x else nilB.

Lemma cursorPointsTo_consBYTE (p:ADDRCursor) (b:BYTE) bs :
  p :-> (b::bs) -|- Exists p', (p = mkCursor p' /\\ p' :-> b ** (next p') :-> bs).
Proof.
elim p => [p' |]. rewrite pointsTo_consBYTE. split.  apply lexistsR with p'. sbazooka.
sdestructs => p0 [->]. sbazooka.
rewrite topPointsTo_consBYTE.
split => //.
by sdestructs => p' H.
Qed.

(* TODO: this seems like we should use the n.-tuple BYTE reader here *)
Lemma pointsToDWORD_BYTES (p:ADDR) (b0 b1 b2 b3:BYTE):
  p :-> [::b0;b1;b2;b3] -|- p :-> (b3 ## b2 ## b1 ## b0).
Proof.
Admitted.
(*rewrite {2}/pointsTo.
rewrite /memIs/readerMemIs/readNext/readDWORD.
split => //.

ssplit.

rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. ssplit.
rewrite cursorPointsTo_consBYTE. sdestructs => p0 H0. rewrite pointsToBYTE_byteIs.
rewrite cursorPointsTo_consBYTE. sdestructs => p1 H1. rewrite pointsToBYTE_byteIs.
rewrite cursorPointsTo_consBYTE. sdestructs => p2 H2. rewrite pointsToBYTE_byteIs.
rewrite seqPointsToNil.
rewrite H0. setoid_rewrite interpReader_bindBYTE. ssplit.
rewrite H1. setoid_rewrite interpReader_bindBYTE. ssplit.
rewrite H2. setoid_rewrite interpReader_bindBYTE. ssplit.
setoid_rewrite interpReader_retn.
rewrite /bytesToDWORD.
sbazooka.
have H0':= (nextIsInc H0).
have H1':= (nextIsInc H1).
have H2':= (nextIsInc H2).
subst. reflexivity.


sdestruct => q.
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b0'.
case E: (next p) => [p' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b1'.
case E': (next p') => [p'' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b2'.
case E'': (next p'') => [p''' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b3'.
rewrite interpReader_retn.
rewrite -> seqPointsToNil.
rewrite /bytesToDWORD.
sdestructs => H1 H2. ssimpl.
destruct (catB_inj (n1:=8) (n2:=24) H2) as [H2a H2'].
destruct (catB_inj (n1:=8) (n2:=16) H2') as [H2b H2''].
destruct (catB_inj (n1:=8) (n2:=8) H2'') as [H2c H2d].
subst. by ssimpl.

rewrite interpReader_bindBYTE_top. by ssimpl.
rewrite interpReader_bindBYTE_top. by ssimpl.
rewrite interpReader_bindBYTE_top. by ssimpl.
Qed.
*)

Corollary pointsToDWORD_asBYTES (d: DWORD) (p:ADDR):
  let: (b3,b2,b1,b0) := split4 8 8 8 8 d in
  p :-> [::b0;b1;b2;b3] -|- p :-> d.
Proof.
have SE := @split4eta 8 8 8 8 d.
elim E: (split4 8 8 8 8 d) => [[[b3 b2] b1] b0].
rewrite E in SE. rewrite -SE. apply pointsToDWORD_BYTES.
Qed.

Lemma pointsToWORD_BYTES (p:ADDR) (b0 b1:BYTE):
  p :-> [::b0;b1] -|- p :-> (b1 ## b0).
Proof.
Admitted.
(*rewrite {2}/pointsTo.
rewrite /memIs/readerMemIs/readNext/readWORD.
split => //.

ssplit.

rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. ssplit.
rewrite cursorPointsTo_consBYTE. sdestructs => p0 H0. rewrite pointsToBYTE_byteIs.
rewrite seqPointsToNil.
rewrite H0. setoid_rewrite interpReader_bindBYTE. ssplit.
setoid_rewrite interpReader_retn.
rewrite /bytesToWORD.
sbazooka.
have H0':= (nextIsInc H0).
subst. reflexivity.


sdestruct => q.
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b0'.
case E: (next p) => [p' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b1'.
rewrite interpReader_retn.
rewrite -> seqPointsToNil.
rewrite /bytesToWORD.
sdestructs => H1 H2. ssimpl.
destruct (catB_inj (n1:=8) (n2:=8) H2) as [H2c H2d].
subst. by ssimpl.

rewrite interpReader_bindBYTE_top. by ssimpl.
Qed.
*)
Corollary pointsToWORD_asBYTES (d: WORD) (p:ADDR):
  let: (b1,b0) := split2 8 8 d in
  p :-> [::b0;b1] -|- p :-> d.
Proof.
split; rewrite pointsToWORD_BYTES. rewrite {3}(@split2eta 8 8 d); reflexivity. 
rewrite {1}(@split2eta 8 8 d); reflexivity. 
Qed. 


Lemma fixedSizeReader_bind T1 T2 (r1: Reader T1) (r2: T1 -> Reader T2) n1 n2 :
  fixedSizeReader r1 n1 ->
  (forall x, fixedSizeReader (r2 x) n2) ->
  fixedSizeReader (readerBind r1 r2) (n1+n2).
Proof. move => F1 F2.
move => p q v.
rewrite /fixedSizeReader in F1, F2. rewrite interpReader_bind.
sdestructs => p' v1. rewrite -> F1.
sdestruct => E1.
rewrite -> F2.
sdestruct => E2.
have A := (apart_addn E1 E2). sbazooka.
Qed.

Lemma fixedSizeReader_bind_retn T1 T2 (r1: Reader T1) n1 (f: T1 -> T2) :
  fixedSizeReader r1 n1 ->
  fixedSizeReader (readerBind r1 (fun x => readerRetn (f x))) n1.
Proof. move => F1.
move => p q v.
rewrite /fixedSizeReader in F1. rewrite interpReader_bind.
sdestructs => p' v1. rewrite -> F1.
sdestruct => E1.
rewrite interpReader_retn.
sbazooka. subst. done. erewrite interpReader_retn. sbazooka.
Qed.

Lemma fixedSizeReader_retn T (x:T) : fixedSizeReader (readerRetn x) 0.
Proof. rewrite /fixedSizeReader. move => p q v. simpl. sbazooka. Qed.

Lemma fixedSizeDWORD : fixedSizeReader readDWORD 4.
Proof.
  rewrite /fixedSizeReader. move => p q b.
  do 4 apply (fixedSizeReader_bind fixedSizeBYTE) => ?.
  apply fixedSizeReader_retn.
Qed.

Instance FixedMemIsDWORD : FixedMemIs 4 (readerMemIs DWORD).
Proof. apply fixedSizeDWORD. Qed.

Lemma fixedSizeQWORD : fixedSizeReader readQWORD 8.
Proof.
  rewrite /fixedSizeReader. move => p q b.
  do 8 apply (fixedSizeReader_bind fixedSizeBYTE) => ?.
  apply fixedSizeReader_retn.
Qed.

Instance FixedMemIsQWORD : FixedMemIs 8 (readerMemIs QWORD).
Proof. apply fixedSizeQWORD. Qed.


Lemma fixedSizeWORD : fixedSizeReader readWORD 2.
Proof.
  rewrite /fixedSizeReader. move => p q b.
  rewrite /readWORD.
  apply (fixedSizeReader_bind fixedSizeBYTE) => b0.
  apply (fixedSizeReader_bind fixedSizeBYTE) => b1.
  apply fixedSizeReader_retn.
Qed.

Instance FixedMemIsWORD : FixedMemIs 2 (readerMemIs WORD).
Proof. apply fixedSizeWORD. Qed.

Lemma fixedSizeTupleBYTE n : fixedSizeReader (readTupleBYTE n) n.
Proof.
induction n => //=.
+ by apply fixedSizeReader_retn.
+ apply (fixedSizeReader_bind fixedSizeBYTE) => b0.
  by apply fixedSizeReader_bind_retn.
Qed.

Instance FixedMemIsTupleBYTE n : FixedMemIs n (readerMemIs (n.-tuple BYTE)).
Proof. apply fixedSizeTupleBYTE. Qed.


Corollary memIsDWORD_range (p q: ADDR) (c:DWORD):
  p -- q :-> c -|- q = p +# 4 /\\ p -- q :-> c.
Proof. split; last by sdestruct.
have FMI := FixedMemIsDWORD.  rewrite /FixedMemIs in FMI. specialize (FMI p q c).
etransitivity; first apply FMI. (* Why doesn't rewrite work here? *)
sdestruct => A.
sbazooka. by apply apart_addBn.
Qed.

(*---------------------------------------------------------------------------
   Logical interpretation of writers
  ---------------------------------------------------------------------------*)

Fixpoint interpWriterTm {T} (wt:WriterTm T) (p q: ADDRCursor) (t: T) :=
  match wt with
  | writerRetn t' => t = t' /\\ p = q /\\ empSP
  | writerNext b wt' =>
      (* We can't write beyond the last byte of memory! *)
      if p is mkCursor p'
      then byteIs p' b ** interpWriterTm wt' (next p') q t
      else lfalse
  | writerSkip wt' =>
      if p is mkCursor p'
      then Exists b, byteIs p' b ** interpWriterTm wt' (next p') q t
      else lfalse
  | writerCursor wt' => interpWriterTm (wt' p) p q t
  | writerFail => lfalse
  end.

Lemma interpWriterTm_roundtrip X T (wt: WriterTm T) (R: Reader X) p q x t:
  simrw x p R wt ->
  interpWriterTm wt p q t |-- p -- q :-> x.
Proof.
  intros Hsim. induction Hsim => //; rewrite /interpWriterTm-/interpWriterTm/=.
  - sbazooka.
  - apply lexistsR with b. ssimpl. apply IHHsim.
  - sdestructs => b. apply lexistsR with b. ssimpl. apply IHHsim.
  - done.
  - done.
  - done.
Qed.

Lemma runWriterTm_pointsto T (W: WriterTm T) p q t bytes:
  runWriterTm true W p = Some (t, bytes) ->
  p -- q :-> bytes |-- interpWriterTm W p q t.
Proof.
  revert p bytes. induction W => p bytes //.
  - case => <- <- /=. sdestruct => ->. sbazooka.
  - destruct p as [p|]; last done.
    remember (runWriterTm true W (next p)) as runw.
    destruct runw as [[q' bytes']|] => // Hinj.
    rewrite /= in Hinj. rewrite -Heqrunw in Hinj. rewrite /interpWriterTm-/interpWriterTm.
    injection Hinj => ? ? {Hinj}. subst bytes q'.
    rewrite <- (IHW _ bytes'); last by rewrite Heqrunw.
    rewrite ->memIs_consBYTE, ->pointsToBYTE_byteIs. reflexivity.
    simpl in Hinj. by rewrite -Heqrunw in Hinj.
  - destruct p => //= H.
    case E: (runWriterTm true W (next p)) => [[x bytes'] |].
    * rewrite E in H. injection H => [H1 H2]. subst. specialize (IHW _ _ E).
      simpl. apply lexistsR with #0. sdestructs => q1 b' H1 H2. subst.
      sbazooka.
    * by rewrite E in H.
  - move => /=SF. apply: H => //.
Qed.

Lemma interpWriterTm_bind {X Y} (w1: WriterTm X) (w2: X -> WriterTm Y) p q y:
  interpWriterTm (let! x = w1; w2 x) p q y -|-
  Exists p', Exists x, interpWriterTm w1 p p' x ** interpWriterTm (w2 x) p' q y.
Proof.
  revert p. induction w1 => p //=.
  - sbazooka. subst. sbazooka.
  - destruct p.
    * split.
      - rewrite IHw1. by sbazooka.
      - sdestructs => p' v. rewrite IHw1. by sbazooka.
    * split; first done. by sbazooka.
  - destruct p.
    * split.
      - sdestruct => b. rewrite IHw1. by sbazooka.
      - sdestructs => p' v b. apply lexistsR with b. rewrite IHw1. by sbazooka.
    * split; first done. by sbazooka.
  - split; first done. by sbazooka.
Qed.

Lemma interpWriterTm_retn {X} (p q: ADDRCursor) (t t':X) :
  interpWriterTm (writerRetn t) p q t' -|- (t' = t /\\ p = q /\\ empSP).
Proof.  simpl. reflexivity. Qed.

Lemma interpWriterTm_getWCursor (p q r: ADDRCursor) :
  interpWriterTm getWCursor p q r -|- p = q /\\ q = r /\\ empSP.
Proof. simpl. split; sdestructs => H1 H2; subst; sbazooka. Qed.

Lemma interpWriterTm_writerFail (p q: ADDRCursor) :
  interpWriterTm writerFail p q tt -|- lfalse.
Proof. reflexivity. Qed.


Lemma interpWriterTm_top T (wt: WriterTm T) t (q: ADDR) :
  interpWriterTm wt (top _) q t -|-
  lfalse.
Proof.
  split; last done. induction wt => //=.
  sdestructs. discriminate.
Qed.

(* This could also be an instance of memIs just like readerMemIs, but we don't
   want typeclass resolution to be ambiguous. *)
Definition interpWriter X {W: Writer X} (p q: ADDRCursor) (x: X) :=
  interpWriterTm (W x) p q tt.

Lemma interpWriter_roundtrip X (W: Writer X) (R: Reader X)
      {RT: Roundtrip R W} p q x:
  interpWriter p q x |-- p -- q :-> x.
Proof.
  exact: interpWriterTm_roundtrip.
Qed.

Lemma runWriter_interpWriter X (W: Writer X) p q bytes x:
  runWriter true writeNext p x = Some bytes ->
  p -- q :-> bytes |-- interpWriter p q x.
Proof.
  rewrite /interpWriter /runWriter /writeNext => H. simpl in H.
  apply: runWriterTm_pointsto.
  destruct (runWriterTm _ (W x) p) as [[[] bytes']|] => //. by congruence.
Qed.


(*---------------------------------------------------------------------------
   memAny: memory whose value we don't care about
  ---------------------------------------------------------------------------*)

Definition memAny p q := Exists bs: seq BYTE, p -- q :-> bs.

Lemma memAnyEmpty p : empSP |-- memAny p p.
Proof. apply lexistsR  with nil. simpl. sbazooka. Qed.

Lemma memAnyMerge p q r : memAny p q ** memAny q r |-- memAny p r.
Proof.
  rewrite /memAny. sdestructs => s1 s2.

  apply lexistsR with (s1 ++ s2). setoid_rewrite seqMemIsCat.
  rewrite -> pairMemIsPair.
  by apply lexistsR with q.
Qed.

Lemma entails_memAnyNext (p: ADDR) q :
  ltCursor p q -> memAny p q |-- Exists b: BYTE, p :-> b ** memAny (next p) q.
Proof.
  rewrite -leCursor_next.
  move => LT.
  rewrite /memAny. sdestruct => bs.
  destruct bs.
  rewrite -> seqMemIsNil.
  sdestructs => EQ.
  rewrite <- EQ in LT.
  rewrite leCursor_next in LT.
  rewrite /ltCursor in LT.
  rewrite ltB_nat in LT. by rewrite ltnn in LT.

  rewrite -> seqMemIsCons.
  sdestruct => q'. apply lexistsR with b.
  rewrite /pointsTo.
  rewrite -> memIsBYTE_next_entails. sdestructs => ->. sbazooka.
Qed.

Lemma entails_memAnySplit p q r :
  leCursor p q -> leCursor q r -> memAny p r |-- memAny p q ** memAny q r.
Proof.
move/LeCursorP. elim.
  - move=> _. rewrite <-empSPL at 1. ssimpl. apply lexistsR with nil.
    rewrite seqMemIsNil. sbazooka.
  - move => {q} q Hpq Hind Hqr. rewrite leCursor_next in Hqr.
    etransitivity; [apply Hind|]; first exact: leCursor_weaken.
    rewrite ->entails_memAnyNext; last done.
    sdestruct => b. ssimpl.
    rewrite {1}/memAny. sdestructs => s.
    rewrite /memAny. apply lexistsR with (s ++ [:: b]).
    rewrite -> seqMemIsCat. rewrite -> pairMemIsPair.
    apply lexistsR with q. cancel2. rewrite -> seqMemIsCons.
    apply lexistsR with (next q). rewrite -> seqMemIsNil.
    rewrite /pointsTo. sdestruct => q'. rewrite -> memIsBYTE_next_entails.
    sdestructs => ->. sbazooka.
Qed.

Corollary memAnySplit p q r :
  leCursor p q -> leCursor q r -> memAny p r -|- memAny p q ** memAny q r.
Proof. move => H1 H2.
split. by apply entails_memAnySplit. by apply memAnyMerge.
Qed.

Lemma byteIs_entails_memAny (p:ADDR)  b : byteIs p b |-- memAny p (next p).
Proof. rewrite /memAny. apply lexistsR with (b::nil).
simpl. apply lexistsR with (next p). sbazooka.
Qed.

Lemma readerMemIs_entails_memAny R {r: Reader R} : forall p q (v: R),
  p -- q :-> v |-- memAny p q.
Proof. rewrite /memIs/=/readNext.
induction r =>  p q v//=.
+ sdestructs => H ->. apply memAnyEmpty.
+ destruct p => //=. sdestruct => b.
  rewrite -> H. rewrite -> byteIs_entails_memAny.
  by rewrite -> memAnyMerge.
+ destruct p => //=. sdestruct => b.
  rewrite -> IHr. rewrite -> byteIs_entails_memAny.
  by rewrite -> memAnyMerge.
Qed.

Lemma four X (bs: seq X) : size bs = 4 -> exists b1 b2 b3 b4, bs = [::b1;b2;b3;b4].
move => H.
destruct bs => //.
destruct bs => //.
destruct bs => //.
destruct bs => //.
exists x, x0, x1, x2.
destruct bs => //.
Qed.

(*
Lemma memAny_entails_fixedReaderMemIs R {r: Reader R} n : fixedSizeReader r n ->
  forall p q, apart n p q ->
  memAny p q |-- Exists v:R, p :-> v.
Proof.
move => F p q A.
rewrite /memAny. sdestruct => bs.
destruct p => //.
destruct q => //.
rewrite -> (apart_addBn A). setoid_rewrite seqMemIsBYTE_addn.
done. sdestruct => EQ.
destruct (four EQ) as [b0 [b1 [b2 [b3 H]]]]. rewrite H.
apply lexistsR with (b3 ## b2 ## b1 ## b0).
rewrite <- pointsToDWORD_BYTES. rewrite /pointsTo. ssplit.
reflexivity.
Qed.
*)

Lemma memAny_entails_pointsToDWORD (p:ADDR) :
  memAny p (p+#4) |-- Exists d:DWORD, p :-> d.
Proof.
rewrite /memAny. sdestruct => bs.
setoid_rewrite seqMemIsBYTE_addn; last done. sdestruct => EQ.
destruct (four EQ) as [b0 [b1 [b2 [b3 H]]]]. rewrite H.
apply lexistsR with (b3 ## b2 ## b1 ## b0).
rewrite <- pointsToDWORD_BYTES. rewrite /pointsTo. ssplit.
reflexivity.
Qed.

Inductive AnyMemT := AnyMem.


Lemma memAnyLe p q : memAny p q |-- leCursor p q /\\ memAny p q.
Proof. rewrite /memAny. sdestruct => bs. rewrite -> memIsLe. sbazooka. Qed.

Instance AnyMemIs : MemIs AnyMemT.
refine (@Build_MemIs _ (fun p q _ => memAny p q) _).
move => p q _. apply memAnyLe.
Qed.


(* Without this, the Qed check after memAnySplitAdd loops forever. *)
Local Opaque leB.

Corollary memAnySplitAdd (p:ADDR) m1 m2 :
  m1 + m2 < 2 ^ naddrBits ->
  memAny p (p+#(m1+m2)) -|- memAny p (p+#m1) ** memAny (p+#m1) (p+#(m1+m2)).
Proof. move => BOUND.
split.
+ rewrite -> (@memAnyLe). sdestruct => MAL.
apply entails_memAnySplit.
rewrite -{1}(addB0 p). apply (leB_bounded_weaken BOUND) => //. apply leq_addr.
apply (leB_bounded_weaken BOUND) => //. apply leq_addr.

+ apply memAnyMerge.
Qed.


Lemma byteIs_disjoint p1 p2 v1 v2 : byteIs p1 v1 ** byteIs p2 v2 |-- p1 <> p2 /\\ (byteIs p1 v1 ** byteIs p2 v2).
Proof. case E: (p1 == p2). rewrite (eqP E). by setoid_rewrite byteIs_same at 1.
ssplit; last done. move => H. by rewrite H eq_refl in E.
Qed.

