Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.fintype Ssreflect.eqtype Ssreflect.tuple.
Require Import Coq.Strings.String.
Require Import x86proved.cast x86proved.codec x86proved.regex.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.RelationClasses.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*======================================================================================
  Transformation to regular expressions
  ======================================================================================*)
Fixpoint codecToRegex t (c:Codec t) : Regex _ :=
match c with
| Any => RAny _
| Emp => REmp _
| Sym b => RSym b
| Void _ => RVoid _
| Cast _ _ f c => codecToRegex c
| Seq _ _ c d => rSeq (codecToRegex c) (codecToRegex d)
| Alt _ c d => rAlt (codecToRegex c) (codecToRegex d)
| Star _ c => RStar (codecToRegex c)
end.

Lemma starFreeCodec t (c: Codec t) : finiteCodec c -> starfree (codecToRegex c).
Proof. induction c => //=.
rewrite finiteCodecSeq. move => [C1 C2].
apply starfreerSeq; firstorder.
rewrite finiteCodecAlt. move => [C1 C2].
apply starfreerAlt; firstorder.
by rewrite /finiteCodec.
Qed.

Lemma CondToRegex t u (c: Codec t) (d: Codec u):
codecToRegex (SumCond c d) =
  rAlt (rSeq (RSym false) (codecToRegex c)) (rSeq (RSym true) (codecToRegex d)).
Proof. done. Qed.

Lemma rinterpsCodec t (c: Codec t) :
  (forall l v, interp c l v -> rinterp (codecToRegex c) l) ->
  forall v l, interps (interp c) l v -> rinterp (RStar (codecToRegex c)) l.
Proof. move => H. induction v => l /=I.
+ by rewrite I rinterpRStar.
+ rewrite rinterpRStar. destruct I as [s [l1 [l2 [H1 [H2 H3]]]]]. subst.
  exists l1, l2. firstorder.
Qed.

(* Need to apply IH to strictly smaller list but not necessarily to the tail *)
(* Hence more complex formulation using bound on size *)
Lemma rinterpsCodecConvAux t (c: Codec t) :
  (forall l, rinterp (codecToRegex c) l -> exists v, interp c l v) ->
  forall n, forall l, size l <= n -> rinterp (RStar (codecToRegex c)) l ->
  exists v, interps (interp c) l v.
Proof. move => H. induction n.
+ move => l S I. exists nil. destruct l => //.
+ move => l S /=I.
  destruct l => //. by exists nil.
  rewrite /=ltnS in S.
  rewrite -> rinterpRStar in I.
  destruct I as [l1 [l2 [H1 [H2 H3]]]].
  destruct (H _ H2) as [v H0].
  specialize (IHn l2).
  subst. rewrite size_cat in S.
  have LE: size l2 <= n. apply: leq_trans S. by apply leq_addl.
  specialize (IHn LE H3).
  destruct IHn as [vs I].
  exists (v::vs).
  simpl.
  exists s, l1, l2. firstorder.
Qed.

Corollary rinterpsCodecConv t (c: Codec t) :
  (forall l, rinterp (codecToRegex c) l -> exists v, interp c l v) ->
  forall l, rinterp (RStar (codecToRegex c)) l ->
  exists v, interps (interp c) l v.
Proof.  move => H l I.
apply (@rinterpsCodecConvAux t c H (size l)) => //.
Qed.

Lemma rinterpCodec t (c: Codec t) : forall l, (exists v, interp c l v) <-> rinterp (codecToRegex c) l.
Proof. induction c => l.
(* Any *)
rewrite /= rinterpRAny.
split => [[b H] | [b H]]. subst. by exists b.
subst. by exists b.
(* Sym *)
rewrite /= rinterpRSym.
split => [[[] H] | H] //=.
(* Emp *)
rewrite /= rinterpREmp.
split => [[[] H] | H] //=.
(* Void *)
rewrite /= rinterpRVoid. firstorder.
(* Seq *)
rewrite /= rSeqDef rinterpRSeq. split => //=.
move => [[v1 v2] H].
destruct H as [l1 [l2 [H1 [H2 H3]]]]. exists l1, l2.
split => //.
split.
apply (proj1 (IHc1 _)). by exists v1.
apply (proj1 (IHc2 _)). by exists v2.
move => [l1 [l2 [H1 [H2 H3]]]].
have I1 := (proj2 (IHc1 _) H2).
have I2 := (proj2 (IHc2 _) H3).
destruct I1 as [v1 I1].
destruct I2 as [v2 I2].
exists (v1,v2). exists l1, l2.
intuition.
(* Dep *)
(* Alt *)
rewrite /= rAltDef rinterpRAlt.
split => //=.
move => [v H].
destruct H. left. firstorder.
right. firstorder.
move => H.
destruct H.
destruct (proj2 (IHc1 _) H) as [v' H']. exists v'. by left.
destruct (proj2 (IHc2 _) H) as [v' H']. exists v'. by right.
(* Star *)
split => //=.
+ move => [v H]. apply: rinterpsCodec H => l0 v0 I. apply IHc. firstorder.
+ apply: rinterpsCodecConv => l0 I. by apply IHc.
(* Cast *)
rewrite <- IHc. split => //.
move => [v H]. rewrite -> interpCast in H. destruct H as [w [H1 H2]]. subst. by exists w.
move => [w I1]. exists (c w). rewrite interpCast. by exists w.
Qed.

(* Syntactic notion of non-ambiguous *)
Fixpoint NonAmbiguous t (c: Codec t) :=
match c with
| Alt _ c d =>
  (NonOverlapping (codecToRegex c) (codecToRegex d) &&
   NonOverlapping (codecToRegex d) (codecToRegex c)) &&
  (NonAmbiguous c && NonAmbiguous d)
| Seq _ _ c d => NonAmbiguous c && NonAmbiguous d
| Cast _ _ _ c => NonAmbiguous c
| Star _ c => false
| _ => true
end.

Lemma NonAmbiguousFinite t (c: Codec t) : NonAmbiguous c -> finiteCodec c.
Proof. induction c => //=.
move/andP => [N1 N2]. rewrite finiteCodecSeq. split; [by apply IHc1 | by apply IHc2].
move/andP => [/andP[N1a N1b] /andP[N2a N2b]].
rewrite finiteCodecAlt. split; [by apply IHc1 | by apply IHc2].
Qed.

(* Non-trivial proof: if codec c is syntactically non-ambiguuous,
   then codec is deterministic and prefix-free *)
Lemma nonAmbiguousDet t (c: Codec t) : NonAmbiguous c -> dpfInterp c.
Proof. rewrite /dpfInterp. induction c => NA l e v w /=; autorewrite with interp; move =>Iv Iw.
(* Any *)
subst. simpl in Iw. by injection Iw => ->.
(* Sym *)
destruct v. destruct w.
subst. by injection Iw => ->.
(* Emp *)
destruct v. destruct w. subst.
firstorder.
(* Void *)
done.
(* Seq *)
simpl in NA.
destruct (andP NA) as [NA1 NA2].
specialize (IHc1 NA1). specialize (IHc2 NA2).
destruct v as [v1 v2]. destruct w as [w1 w2].
destruct Iv as [l1 [l2 [H3a [H3b H3c]]]].
destruct Iw as [l3 [l4 [H4a [H4b H4c]]]].
subst.
rewrite -catA in H4a. have AP := appeqpref H4a.
destruct AP.
+ destruct H as [e' [E1 E2]]. subst. simpl in *.
 destruct (IHc1 _ _ _ _ H4b H3b) as [H1 H2]. subst. simpl in *. rewrite cats0 in H3b.
 destruct (IHc2 _ _ _ _ H3c H4c) as [H3 H4]. by subst.
+ destruct H as [e' [E1 E2]]. subst. simpl in *.
  destruct (IHc1 _ _ _ _ H3b H4b) as [H1 H2]. subst. simpl in *. subst.
  destruct (IHc2 _ _ _ _ H3c H4c) as [H1 H2]. by subst.
(* Alt *)
simpl in NA. destruct (andP NA) as [NO NA12].
destruct (andP NO) as [NO1 NO2].
destruct (andP NA12) as [NA1 NA2].
specialize (IHc1 NA1). specialize (IHc2 NA2).
apply NonOverlappingSound in NO1. apply NonOverlappingSound in NO2.
rewrite /nonOverlapping in NO1, NO2.
destruct Iv.
+ destruct Iw.
  - by apply (IHc1 _ _ _ _ H H0).
  - contradiction (NO1 l e).
    * apply rinterpCodec. by exists v.
    * apply rinterpCodec. by exists w.
+ destruct Iw.
  - contradiction (NO2 l e).
    * apply rinterpCodec. by exists v.
    * apply rinterpCodec. by exists w.
  - by apply (IHc2 _ _ _ _ H H0).
apply starFreeCodec.
apply NonAmbiguousFinite => //.
apply starFreeCodec.
apply NonAmbiguousFinite => //.
apply starFreeCodec.
apply NonAmbiguousFinite => //.
apply starFreeCodec.
apply NonAmbiguousFinite => //.
(* Star *)
done.
(* Cast *)
destruct Iv as [v1 [E1 I1]].
destruct Iw as [v2 [E2 I2]].
simpl in NA. specialize (IHc NA).
specialize (IHc _ _ _ _ I1 I2). subst. destruct IHc as [H1 H2]. by subst.
Qed.

Lemma decSoundNo t (c: Codec t) :
  NonAmbiguous c ->
  forall l e x, dec c (l++e) = DecNo ->
  ~interp c l x.
Proof. induction c => NA l e x /=; autorewrite with interp => EQ I.
(* Any *)
by destruct l.
(* Sym *)
subst. simpl in EQ. by rewrite eq_refl in EQ.
(* Emp *)
done.
(* Void *)
done.
(* Seq *)
simpl in NA. destruct (andP NA) as [NA1 NA2].
destruct x as [x1 x2].
case E1: (dec c1 (l++e)) => [x l' |]; rewrite E1 in EQ => //.
(* First decode succeeds *)
- case E2: (dec c2 l') => [y l'' |]; rewrite E2 in EQ => //.
  (* Second decode fails *)
  destruct I as [l1 [l2 [E [I1 I2]]]]. simpl in I1, I2. subst. clear EQ.
  rewrite -catA in E1. destruct (decSound E1) as [e' [H1 H2]].
  have DET1 := nonAmbiguousDet NA1. rewrite /dpfInterp in DET1.
  have AP := appeqpref H1.
  destruct AP.
  - destruct H as [e0 [H3 H4]]. subst.
    destruct (DET1 _ _ _ _ H2 I1) as [D1 D2]. subst.
    simpl in E2. by specialize (IHc2 NA2 _ _ x2 E2).
  - destruct H as [e0 [H3 H4]]. subst.
    destruct (DET1 _ _ _ _ I1 H2) as [D1 D2]. subst. simpl in H4. subst.
    by specialize (IHc2 NA2 _ _ x2 E2).
(* First decode fails *)
destruct I as [l1 [l2 [E [I1 I2]]]]. simpl in I1, I2. subst.
rewrite -catA in E1.
by specialize (IHc1 NA1 _ _ x1 E1).
(* Alt *)
simpl in NA. destruct (andP NA) as [NO NA12].
destruct (andP NA12) as [NA1 NA2]. specialize (IHc1 NA1). specialize (IHc2 NA2).
case E1: (dec c1 (l++e)) => [x' l' |]; rewrite E1 in EQ => //.
destruct I.
by specialize (IHc1 _ _ _ E1 H).
by specialize (IHc2 _ _ _ EQ H).
(* Star *)
done.
(* Cast *)
case E1: (dec c0 (l++e)) => [x' l' |]; rewrite E1 in EQ => //.
destruct I as [w [E2 E3]]. subst.
by specialize (IHc NA _ _ _ E1 E3).
Qed.


Lemma CodecComplete : forall t (c: Codec t),
  NonAmbiguous c ->
  forall l x, interp c l x ->
  forall e, dec c (l ++ e) = DecYes x e.
Proof.
induction c => NA l x /=; autorewrite with interp => I e.
(* Any *)
by subst.
(* Sym *)
destruct x. autorewrite with interp in I.
subst. simpl. by rewrite eq_refl.
(* Emp *)
destruct x. autorewrite with interp in I.
by subst.
(* Void *)
done.
(* Seq *)
simpl in NA. destruct (andP NA) as [NA1 NA2].
destruct x as [x1 x2].
destruct I as [l1 [l2 [E [I1 I2]]]]. simpl in I1, I2.
specialize (IHc1 NA1 _ _ I1).
specialize (IHc2 NA2 _ _ I2).
by rewrite E -catA IHc1 IHc2.
(* Alt *)
simpl in NA. destruct (andP NA) as [NO NA12].
destruct (andP NA12) as [NA1 NA2].
destruct (andP NO) as [NO1 NO2].
apply NonOverlappingSound in NO1. rewrite /nonOverlapping in NO1.
apply NonOverlappingSound in NO2. rewrite /nonOverlapping in NO2.
(* OK, we have that [[c2]] contains (l,x) *)
case E: (dec c1 (l++e)) => [r l' |].

destruct I.
by rewrite (IHc1 NA1 _ _ H) in E.

destruct (decSound E) as [l1 [E' I]].
clear E.
have AE := appeqpref E'.
destruct AE.
destruct H0 as [e' [H1 H2]]. subst. clear E'.

contradiction (NO1 l1 e'). apply rinterpCodec. by exists r.
apply rinterpCodec. by exists x.
destruct H0 as [e' [H1 H2]]. subst. clear E'.
contradiction (NO2 l e').
apply rinterpCodec. by exists x.
apply rinterpCodec. by exists r.

destruct I.
by have S := decSoundNo NA1 E H.
apply IHc2 => //.
apply starFreeCodec.
apply NonAmbiguousFinite => //.
apply starFreeCodec.
apply NonAmbiguousFinite => //.
apply starFreeCodec.
apply NonAmbiguousFinite => //.
apply starFreeCodec.
apply NonAmbiguousFinite => //.
(* Star *)
done.
(* Cast *)
destruct I as [v [E I]].
specialize (IHc NA _ _ I). rewrite IHc. by subst.
Qed.

Corollary CodecRoundtrip t (c: Codec t) l e x:
  NonAmbiguous c ->
  enc c x = Some l ->
  dec c (l ++ e) = DecYes x e.
Proof. move => NA ENC. apply CodecComplete => //. by apply encSound. Qed.
