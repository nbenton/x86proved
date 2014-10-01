(*===========================================================================
    In order to formalize memory ranges, and reading the very last byte in
    memory, we introduce a type of Cursor, which is either an actual
    address or the address beyond the top of memory. In other words, this is
    just [0..2^n] where n is the number of bits in an address.
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.finfun Ssreflect.eqtype Ssreflect.fintype Ssreflect.tuple Ssreflect.seq.
Require Import Ssreflect.choice Ssreflect.tuple Ssreflect.div.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.bitsops x86proved.bitsopsprops x86proved.nathelp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Cursors.

(*=Cursor *)
Variable n:nat.
Inductive Cursor := mkCursor (p: BITS n) | top.
(*=End *)

(* Embedding into nat -- for proofs only! *)
Definition cursorToNat pos := if pos is mkCursor p then toNat p else 2^n.

(*---------------------------------------------------------------------------
    next: BITS n -> Cursor n
    and its properties
  ---------------------------------------------------------------------------*)
Definition next (p:BITS n) := if p == ones _ then top else mkCursor (incB p).

Definition nextCursor (p:Cursor) :=
  if p is mkCursor pos then next pos else top.

Lemma nextIsInc (p q: BITS n) : next p = mkCursor q -> p+#1 = q.
Proof. rewrite /next. move => EQ.
case E: (p == ones n). rewrite E in EQ. done.
rewrite E in EQ. rewrite addB1. congruence.
Qed.

Lemma nextIsTop (p: BITS n) : next p = top -> p+#1 = #0.
Proof. rewrite /next. move => EQ.
case E: (p == ones n). rewrite E in EQ. rewrite (eqP E).
rewrite addB1. rewrite incB_ones. by rewrite fromNat0.
by rewrite E in EQ.
Qed.


Lemma cursorToNat_next pos : cursorToNat (next pos) = (toNat pos).+1.
Proof. rewrite /next. case TOP: (pos == ones _).
+ simpl. rewrite (eqP TOP). rewrite toNat_ones. rewrite prednK => //. apply expn_gt0.
+ rewrite /cursorToNat. rewrite toNat_incB. by rewrite TOP.
Qed.

Lemma cursorToNat_inj: injective cursorToNat.
Proof.
  move => [p|] [q|] /= H.
  - f_equal. exact: toNat_inj.
  - have Hlt := toNatBounded p. rewrite H in Hlt.
    move/ltP: Hlt. intros. exfalso. omega.
  - have Hlt := toNatBounded q. rewrite -H in Hlt.
    move/ltP: Hlt. intros. exfalso. omega.
  - done.
Qed.

Lemma cursorToNatBounded : forall (c: Cursor), cursorToNat c <= 2^n.
Proof. elim => [b |] => //. rewrite /=. apply ltnW. apply toNatBounded. Qed.

(*---------------------------------------------------------------------------
    Order relations on Cursor
  ---------------------------------------------------------------------------*)
Definition ltCursor (pos1 pos2: Cursor) :=
  match pos1, pos2 with
  | top, _ => false
  | mkCursor p1, mkCursor p2 => ltB p1 p2
  | mkCursor _, top => true
  end.
Definition leCursor (pos1 pos2: Cursor) :=
  match pos1, pos2 with
  | _, top => true
  | top, mkCursor _ => false
  | mkCursor p1, mkCursor p2 => leB p1 p2
  end.

Lemma ltCursor_nat pos1 pos2 : ltCursor pos1 pos2 = (cursorToNat pos1 < cursorToNat pos2).
Proof. destruct pos1 => //. destruct pos2 => //. by rewrite /=ltB_nat.
simpl. by rewrite toNatBounded.
destruct pos2 => //.
simpl. symmetry. apply negbTE. rewrite -leqNgt. apply ltnW. apply toNatBounded.
simpl. by rewrite ltnn.
Qed.

Lemma leCursor_nat pos1 pos2 : leCursor pos1 pos2 = (cursorToNat pos1 <= cursorToNat pos2).
Proof. destruct pos1 => //. destruct pos2 => //. by rewrite /=leB_nat.
simpl. symmetry. apply ltnW. apply toNatBounded.
destruct pos2 => //.
simpl. symmetry. apply negbTE. rewrite -ltnNge. apply toNatBounded.
simpl. by rewrite leqnn.
Qed.

Lemma ltNext (p:BITS n) : ltCursor (mkCursor p) (next p).
Proof. by rewrite ltCursor_nat cursorToNat_next. Qed.

Lemma leNext (p:BITS n) : leCursor (mkCursor p) (next p).
Proof. by rewrite leCursor_nat cursorToNat_next. Qed.

Lemma leCursor_next (p: BITS n) q: leCursor (next p) q = ltCursor (mkCursor p) q.
Proof. by rewrite leCursor_nat ltCursor_nat cursorToNat_next. Qed.

Lemma leCursor_refl pos : leCursor pos pos.
Proof. by rewrite leCursor_nat. Qed.

Lemma leCursor_weaken pos1 pos2 : ltCursor pos1 pos2 -> leCursor pos1 pos2.
Proof. rewrite ltCursor_nat leCursor_nat. apply ltnW. Qed.

Lemma leCursor_trans pos1 pos2 pos3 : leCursor pos1 pos2 -> leCursor pos2 pos3 -> leCursor pos1 pos3.
Proof. rewrite !leCursor_nat. apply leq_trans. Qed.

Lemma ltCursor_trans pos1 pos2 pos3 : ltCursor pos1 pos2 -> ltCursor pos2 pos3 -> ltCursor pos1 pos3.
Proof. rewrite !ltCursor_nat. apply ltn_trans. Qed.

Lemma ltCursor_leCursor_trans pos1 pos2 pos3 : ltCursor pos1 pos2 -> leCursor pos2 pos3 -> ltCursor pos1 pos3.
Proof. move => H1 H2.
case E1: pos1 => [p1 |]; subst.
case E2: pos2 => [p2 |]; subst.
case E3: pos3 => [p3 |]; last done; subst.
rewrite /ltCursor in H1. rewrite /leCursor in H2.
apply: ltB_leB_trans H1 H2.
case E3: pos3 => [p3 |]; subst; done.
case E2: pos2 => [p2 |]; subst; done.
Qed.

Lemma leCursor_ltCursor_trans pos1 pos2 pos3 : leCursor pos1 pos2 -> ltCursor pos2 pos3 -> ltCursor pos1 pos3.
Proof. rewrite !ltCursor_nat !leCursor_nat. apply leq_ltn_trans. Qed.

Lemma leCursor_Ngt pos1 pos2 : leCursor pos1 pos2 = ~~ (ltCursor pos2 pos1).
Proof. rewrite leCursor_nat ltCursor_nat. apply leqNgt. Qed.


Lemma leCursorNonTop (l: Cursor) (u: BITS n) :
  leCursor l (mkCursor u) -> exists l':BITS n, l = mkCursor l'.
Proof. case E: l => [l' |] //. by exists l'. Qed.

Fixpoint nexts k (c: Cursor) : option (Cursor) :=
  match k , c with
  | 0 , _ => Some c
  | k'.+1 , mkCursor p => nexts k' (next p)
  | k'.+1 , top => None
  end.

(*---------------------------------------------------------------------------
    Apart by n
  ---------------------------------------------------------------------------*)
Fixpoint apart n (p q: Cursor) :=
  match n, p with
  | n'.+1, mkCursor p' => apart n' (next p') q (* q = next (p' +# n)  *)
  | 0, _ => q = p
  | _, _ => False
  end.

Lemma apart_addn n1:
  forall n2 p p' p'', apart n1 p p' -> apart n2 p' p'' -> apart (n1+n2) p p''.
Proof. induction n1 => n2 p p' p'' H1 H2.
+ rewrite add0n. congruence.
+ destruct p => //. simpl in H1. by apply (IHn1 _ _ _ _ H1).
Qed.

Lemma apart_fromTop m q : apart m top q <-> m=0 /\ q=top.
Proof. split. destruct m => //. by move => [-> ->]. Qed.

Lemma apart_toTop m : forall (p: BITS n), apart m (mkCursor p) top -> p +# m = #0. 
Proof. induction m => // p AP. 
simpl in AP. 
case E: (next p) => [p' |]. rewrite E in AP. specialize (IHm _ AP). rewrite -IHm. 
rewrite <- (nextIsInc E). rewrite <- addB_addn. by rewrite add1n. 
rewrite E in AP. destruct m => //. by rewrite (nextIsTop E). 
Qed. 

Lemma apart_next m : forall (p: BITS n) (q: Cursor),
  apart m (next p) q <-> apart m.+1 (mkCursor p) q.
Proof. done. Qed.

Lemma apart_addBn m : forall (p q:BITS n), apart m (mkCursor p) (mkCursor q) -> q = p+#m.
Proof. induction m => p q H.
+ rewrite addB0. congruence.
+ simpl in H.
case E: (next p) => [p' |]; rewrite E in H. specialize (IHm _ _ H).
by rewrite -(nextIsInc E) -addB_addn add1n in IHm. rewrite -> apart_fromTop in H.
by destruct H.
Qed.

Lemma apart_addBn_next m : forall (p:BITS n) (q: Cursor), apart m.+1 (mkCursor p) q -> q = next (p+#m).
Proof. induction m => p q /=AP. by rewrite addB0.
case E: (next p) => [p' |]; rewrite E in AP => //. rewrite -> apart_next in AP.
specialize (IHm _ _ AP). rewrite -(nextIsInc E) in IHm.
by rewrite -addB_addn add1n in IHm.
Qed.

Lemma apart_leCursor m: forall (p q: Cursor), apart m p q -> leCursor p q.
Proof. induction m => p q /=H.
+ subst. apply leCursor_refl.
+ destruct p => //. apply IHm in H. rewrite leCursor_next in H.
by apply leCursor_weaken. Qed.

(*---------------------------------------------------------------------------
    Subtraction
  ---------------------------------------------------------------------------*)
Definition subCursor (p q: Cursor) : Cursor :=
  match p, q with
  | _, top => mkCursor (zero _)
  | mkCursor p', mkCursor q' =>
    if leB p' q' then mkCursor (zero _) else mkCursor (subB p' q')
  | top, mkCursor p' =>
    if p' == zero _ then top else mkCursor (negB p')
  end.


Lemma cursorToNat_sub (p q: Cursor) :
  cursorToNat (subCursor p q) = cursorToNat p - cursorToNat q.
Proof.
elim: p => [p' |] /=.
elim: q => [q' |] /=.
case LE: (leB p' q').
rewrite leB_nat in LE. rewrite /= toNat_zero.
have H := subn_eq0 (toNat p') (toNat q') .
rewrite LE in H. by rewrite (eqP H). simpl. apply toNat_subB.
rewrite leB_nat.
rewrite leB_nat in LE.
have L:= @leq_total (toNat p') (toNat q'). rewrite LE in L. apply L.

have B := toNatBounded p'. rewrite toNat_zero. have H:= subn_eq0 (toNat p') (2^n).
suff: (0 == (toNat p' - 2^n)). move => H'. by rewrite -(eqP H').
rewrite eq_sym H. apply: ltnW B.

elim: q => [q' |] /=.
case E: (q' == zero _).
by rewrite /= (eqP E) toNat_zero subn0.
rewrite /= toNat_negB.
have H1: (0 = (toNat (zero n))). by rewrite toNat_zero.
rewrite {1}H1.
by rewrite -bitsEq_nat E.
by rewrite toNat_zero subnn.
Qed.

Lemma subCursorIsTop (p1 p2: Cursor) : subCursor p1 p2 = top -> p1 = top /\ p2 = mkCursor #0.
Proof. move => H.
elim E1: p1 => [d1 |].
  elim E2: p2 => [d2 |].
  rewrite E1 E2/= in H. by destruct (leB d1 d2).
  by rewrite E1 E2/= in H.
  elim E2: p2 => [d2 |].
  rewrite E1 E2/= in H. case E3: (d2 == zero n). rewrite (eqP E3). split. done.
  by rewrite fromNat0. rewrite E3 in H. by inversion H.
  rewrite E1 E2/= in H. inversion H.
Qed.

(*---------------------------------------------------------------------------
    Range testing
  ---------------------------------------------------------------------------*)
Definition inRange p q := fun p' => leCursor p p' && ltCursor p' q.
Definition outRange p q := fun p' => ltCursor p' p && leCursor q p'.

Lemma inRange_next (p p': BITS n) :
  inRange (mkCursor p) (next p) (mkCursor p') -> p' = p.
Proof.
  rewrite /inRange.
  rewrite leCursor_nat ltCursor_nat cursorToNat_next /= ltnS.
  move=> H. symmetry. apply: toNat_inj. exact: anti_leq.
Qed.

(* If there's a range [p;q[ divided up by a p', then any p'' in that
   range will be either on the left of p' or on the right of p'. *)
Lemma inRange_case (p' p q p'': Cursor):
  inRange p q p'' ->
  leCursor p p' ->
  leCursor p' q ->
  inRange p p' p'' \/ inRange p' q p''.
Proof.
  move/andP => [Hpp'' Hp''q] Hpp' Hp'q.
  case H: (ltCursor p'' p').
  - left. rewrite /inRange. by rewrite H Hpp''.
  - right. rewrite /inRange. by rewrite Hp''q leCursor_Ngt H.
Qed.

(* Together with lemma LeCursorP, this allows doing induction over leCursor.
 *)
Inductive LeCursor p: Cursor -> Prop :=
| LeCursor_refl: LeCursor p p
| LeCursor_next q: LeCursor p (mkCursor q) -> LeCursor p (next q).

(* Only one direction proved for now
Lemma LeCursorP (p q: Cursor n): reflect (LeCursor p q) (leCursor p q).
*)
Lemma LeCursorP p q: leCursor p q -> LeCursor p q.
Proof.
  rewrite leCursor_nat.
  move Hpq: (cursorToNat p <= cursorToNat q) => pq.
  destruct pq (*; constructor *) => [_|H].
  - move/leP: Hpq. move Hp: (cursorToNat p) => np.
    move Hq: (cursorToNat q) => nq. move=> Hpq.
    move: q Hq. induction Hpq as [|nq] => q Hq.
    - have ->: p = q; last by constructor.
      subst. exact: cursorToNat_inj.
    - have [q' Hq']: exists q': BITS n, next q' = q.
      - move: Hq. clear. case: q => /=.
        - move=> q Hq. exists (decB q). rewrite /next.
          rewrite decBK. move HisOnes: (decB q == ones _) => b.
          destruct b; last done. (* now the impossible case *)
          have HdecB: decB q = ones n by apply (eqP HisOnes).
          rewrite -decB_zero in HdecB.
          eapply can_inj in HdecB; last by apply decBK. subst.
          rewrite toNat_zero in Hq. done.
        - move=> _. exists (ones n). unfold next.
          rewrite eq_refl; by [|apply: zero (* TODO: fix the lemma *)].
      subst q. constructor. apply IHHpq. rewrite cursorToNat_next in Hq.
      by injection Hq.
  - done.
Qed.

End Cursors.

Coercion mkCursor : BITS >-> Cursor.

Lemma leB_apart n m : forall (p: BITS n.+1) (q: Cursor n.+1),
  m < 2^n.+1 -> leB p (p +# m) -> apart m (mkCursor p) q -> q = mkCursor (p +# m).
Proof. 
induction m => p q LT LE AP.
- by rewrite AP addB0. 
- simpl in AP. have LT': m < 2^n.+1. apply: (ltn_trans _ LT). by apply ltnSn.
  case E: (next p) => [p' |].
  rewrite E in AP. specialize (IHm p' q LT'). 
  rewrite <- (add1n m). rewrite addB_addn. rewrite -> (nextIsInc E). apply IHm.
  apply nextIsInc in E.  
  subst. rewrite <- addB_addn. rewrite <- (add1n m) in LE.
  apply: (leB_bounded_weaken LT _ _ LE). done. by rewrite add1n.
  done.   
- rewrite E in AP. destruct m => //. rewrite (nextIsTop E) in LE.
  apply le0B in LE. by subst. 
Qed.


Notation DWORDCursor  := (Cursor n32).
Notation QWORDCursor  := (Cursor n64).

Lemma nextCat n1 n2 (p:BITS n1) m : m < (2^n2).-1 ->
  next (p ## fromNat (n:=n2) m) = p ## #(m.+1).
Proof. move => LT.
apply cursorToNat_inj. rewrite cursorToNat_next/=. rewrite 2!toNatCat 2!toNat_fromNat.
rewrite modn_small.
rewrite modn_small. by rewrite -addn1 -addnA addn1.
rewrite -subn1 in LT. rewrite ltn_subRL in LT. by rewrite add1n in LT.
rewrite -subn1 in LT. rewrite ltn_subRL in LT. rewrite add1n in LT.
by apply ltnW in LT.
Qed.

Lemma toNatInjOpp n (x y: BITS n) : x != y -> toNat x != toNat y.
Proof. move/eqP => H. apply/eqP. move => H'. by apply toNat_inj in H'. Qed.

Definition widenCursor n1 n2 (c: Cursor n1) : Cursor (n2+n1) :=
  if c is mkCursor p then mkCursor (p ## zero n2) else top _.

Lemma nextCatNext n1 n2 (p: BITS n1.+1) : next (p ## ones n2) = widenCursor n2 (next p).
Proof. case E: (next p) => [p' |]. rewrite -(nextIsInc E).
apply cursorToNat_inj. rewrite /= cursorToNat_next/=.
rewrite /= 2!toNatCat toNat_zero toNat_ones toNat_addB toNat_fromNat addn0.
rewrite modn_small. rewrite modn_small.
rewrite mulnDl mul1n. rewrite -addn1 -addnA addn1.
rewrite prednK. done. apply expn_gt0. apply pow2_gt1.

rewrite /next in E.
case E': (p == ones _); rewrite E' in E. done.
have: toNat p != (2^(n1.+1)).-1.
rewrite <- toNat_ones. apply toNatInjOpp. by rewrite E'.

have B:= toNatBounded p. move => H. replace (2^n1.+1) with (2^n1.+1).-1.+1.
rewrite prednK. rewrite modn_small.
rewrite addn1.
rewrite ltn_neqAle. apply/andP. split => //.
apply/eqP => H'. rewrite -H' in H. rewrite succnK in H. by move/eqP: H.
apply pow2_gt1.
apply expn_gt0.
rewrite prednK. done.
apply expn_gt0.

apply cursorToNat_inj. rewrite /= cursorToNat_next/=.
rewrite toNatCat toNat_ones.  rewrite -addn1 -addnA addn1.
rewrite prednK.
rewrite /next in E.
case E': (p == ones _); rewrite E' in E => //.
rewrite (eqP E'). rewrite toNat_ones. rewrite expnD.
rewrite -subn1. rewrite mulnBl mul1n.
rewrite subnK. by rewrite mulnC.
rewrite -{1}(mul1n (2^n2)). rewrite leq_mul2r. apply/orP. right. apply expn_gt0.
apply expn_gt0.
Qed.

Lemma widenCursor0 n (p: Cursor n) : widenCursor 0 p = p.
Proof. destruct p => //=. f_equal. apply toNat_inj.
by rewrite toNatCat toNat_zero addn0 expn0 muln1. Qed.

Lemma apart_toNat n m :
  forall (p q: Cursor n), cursorToNat p + m = cursorToNat q <-> apart m p q.
Proof. induction m => // p q.
+ rewrite addn0. split. move => H. by apply: cursorToNat_inj. by move => ->.
+ destruct p => //. destruct (IHm (next p) q) as [I1 I2]. split => AP.
  rewrite -apart_next. apply I1. by rewrite cursorToNat_next -addn1 -addnA add1n.
  rewrite cursorToNat_next in I2. specialize (I2 AP).
  simpl. by rewrite -addn1 -addnCA addnC addn1.
  simpl. split => //. have B:= cursorToNatBounded q.
  move => H. rewrite -H in B. rewrite /= -(add1n m) -addnCA add1n in B.
  rewrite -{2}(addn0 (2^n)) in B.
  by rewrite ltn_add2l in B.
Qed.

Lemma cursorToNat_widen m n (p: Cursor n) :
  cursorToNat (widenCursor m p) = cursorToNat p * 2^m.
Proof. destruct p => /=. by rewrite toNatCat toNat_zero addn0. by rewrite expnD mulnC. Qed.

Lemma apart_widen n2 : forall n1 m (p q: Cursor n1),
  apart m p q -> apart (m*2^n2) (widenCursor n2 p) (widenCursor n2 q).
Proof. move => n1 m p q AP. rewrite -apart_toNat. rewrite <-apart_toNat in AP.
rewrite 2!cursorToNat_widen. by rewrite -AP mulnDl. Qed.

Lemma subCursor_next n (p: BITS n.+1) :
  subCursor (next p) p = fromNat 1.
Proof. apply cursorToNat_inj.
rewrite cursorToNat_sub. rewrite cursorToNat_next.
rewrite /cursorToNat. rewrite subSn => //. rewrite subnn. rewrite toNat_fromNatBounded => //.
apply pow2_gt1.
Qed.

(* Because Cursor is essentially isomorphic to option, we can inherit
   many canonical structures. *)
Section CursorCanonicals.
  Variable n: nat.

  Definition cursor_option (p: Cursor n) : option (BITS n) :=
    if p is mkCursor p' then Some p' else None.

  Definition option_cursor (o: option (BITS n)) : Cursor n :=
    if o is Some p' then mkCursor p' else top n.

  Lemma cursor_optionC: cancel cursor_option option_cursor.
  Proof. by move=> [p|] /=. Qed.

  Definition Cursor_eqMixin := CanEqMixin cursor_optionC.
  Canonical Structure Cursor_eqType :=
    Eval hnf in EqType (Cursor n) Cursor_eqMixin.

  Definition Cursor_countMixin := CanCountMixin cursor_optionC.
  Definition Cursor_choiceMixin := CountChoiceMixin Cursor_countMixin.
  Canonical Structure Cursor_choiceType :=
    Eval hnf in ChoiceType _ Cursor_choiceMixin.
  Canonical Structure Cursor_countType :=
    Eval hnf in CountType _ Cursor_countMixin.

  Definition Cursor_finMixin := Eval hnf in CanFinMixin cursor_optionC.
  Canonical Structure Cursor_finType := Eval hnf in FinType _ Cursor_finMixin.
End CursorCanonicals.
