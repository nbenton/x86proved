Require Import ssreflect ssrfun seq ssrbool ssrnat fintype eqtype choice.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Regex.

Variable sym: eqType.

Inductive Regex :=
| RAny | RSym (sym:sym) | REmp | RVoid | RSeq (r s: Regex) | RAlt (r s: Regex)
| RStar (r: Regex).

(* Size, depth *)
Fixpoint rsize r :=
match r with
| RSeq r1 r2 => 1 + rsize r1 + rsize r2
| RAlt r1 r2 => 1 + rsize r1 + rsize r2
| RStar r => 1 + rsize r
| _ => 1
end.

Fixpoint rdepth r :=
match r with
| RSeq r1 r2 => 1 + max (rdepth r1) (rdepth r2)
| RAlt r1 r2 => 1 + max (rdepth r1) (rdepth r2)
| RStar r => 1 + rdepth r
| _ => 1
end.

(* Smart constructors *)
Fixpoint rSeq r1 r2 :=
match r1, r2 with
| _, RVoid => RVoid
| RVoid, _ => RVoid
| REmp, _ => r2
| _, REmp => r1
| RSeq r1a r1b, _ => RSeq r1a (rSeq r1b r2)
| _, _ => RSeq r1 r2
end.

(* This one does balancing too *)
Fixpoint rAlt r1 r2 :=
match r1, r2 with
| _, RVoid => r1
| RVoid, _ => r2
| RAlt r1a r1b, _ => RAlt r1a (rAlt r1b r2)
| _, _ => RAlt r1 r2
end.

Fixpoint rStar r :=
match r with
| RVoid => REmp
| REmp => REmp
| RStar r => RStar (rStar r)
| _ => r
end.

(*======================================================================================
  Semantic interpretation
  ======================================================================================*)
Inductive rinterp : Regex -> seq sym -> Prop :=
| rinterp_RAny b : rinterp RAny [::b]
| rinterp_REmp : rinterp REmp nil
| rinterp_RSym b : rinterp (RSym b) [::b]
| rinterp_RAlt1 r1 r2 l : rinterp r1 l -> rinterp (RAlt r1 r2) l
| rinterp_RAlt2 r1 r2 l : rinterp r2 l -> rinterp (RAlt r1 r2) l
| rinterp_RSeq r1 r2 l1 l2 : rinterp r1 l1 -> rinterp r2 l2 -> rinterp (RSeq r1 r2) (l1++l2)
| rinterp_RStarNil r : rinterp (RStar r) nil
| rinterp_RStarCons r c l1 l2 : rinterp r (c::l1) -> rinterp (RStar r) l2 -> rinterp (RStar r) (c::(l1++l2)).

Lemma rinterpRAny l :
  rinterp RAny l <-> exists b, l = [::b].
Proof. split => H. inversion H. subst. by exists b.
destruct H. subst. apply rinterp_RAny. Qed.

Lemma rinterpREmp l :
  rinterp REmp l <-> l = nil.
Proof. split => H. by inversion H. subst; constructor.
Qed.

Lemma rinterpRSym b l :
  rinterp (RSym b) l <-> l = [::b].
Proof. split => H. inversion H. by subst.
subst. apply rinterp_RSym. Qed.

Lemma rinterpRVoid l :
  rinterp RVoid l <-> False.
Proof. split => H. inversion H. done. Qed.

Lemma rinterpRAlt (r1 r2: Regex) (l: seq sym) :
  rinterp (RAlt r1 r2) l <-> rinterp r1 l \/ rinterp r2 l.
Proof. split => H. inversion H. by left. by right.
destruct H. by apply rinterp_RAlt1. by apply rinterp_RAlt2. Qed.

Lemma rinterpRSeq (r1 r2: Regex) (l: seq sym) :
  rinterp (RSeq r1 r2) l <-> exists l1 l2, l = l1++l2 /\ rinterp r1 l1 /\ rinterp r2 l2.
Proof. split => H. inversion H. subst. by exists l1, l2.
destruct H as [l1 [l2 [-> [H2 H3]]]].  by constructor. Qed.

Lemma rinterpRSeqSym (r: Regex) s (l: seq sym) :
  rinterp (RSeq (RSym s) r) l <-> exists l', l = s::l' /\ rinterp r l'.
Proof. rewrite rinterpRSeq. simpl.
split. move => [l1 [l2 [H1 [H2 H3]]]]. inversion H2. subst. by exists l2.
move => [l' [H1 H2]]. subst. exists [::s]. exists l'. split => //. split => //. constructor.
Qed.

Lemma rinterpRStar (r: Regex) (l: seq sym) :
  rinterp (RStar r) l <->
  if l is c::l' then
  (exists l1 l2, l' = l1++l2 /\ rinterp r (c::l1) /\ rinterp (RStar r) l2) else True.
Proof. split => H.
+ destruct l => //. inversion H; subst. by exists l1, l2.
+ destruct l => //. constructor.
  destruct H as [l1 [l2 [H1 [H2 H3]]]]. subst. by constructor.
Qed.

Hint Rewrite rinterpRAny rinterpREmp rinterpRSym rinterpRVoid rinterpRAlt
  rinterpRSeqSym rinterpRSeq rinterpRStar : rinterp.

(*======================================================================================
  Semantic equivalence
  ======================================================================================*)
Definition regexEq (r1 r2: Regex) := forall l, rinterp r1 l <-> rinterp r2 l.

Notation "x '===' y" := (regexEq x y) (at level 70, no associativity).

Global Instance regexEqEqu : Equivalence regexEq.
Proof. constructor; red => //.
+ move => r1 r2 H l. firstorder.
+ move => r1 r2 r3 H1 H2 l. firstorder.
Qed.

Global Instance regexEq_RSeq_m: Proper (regexEq ==> regexEq ==> regexEq) RSeq.
Proof. move => r1 r2 EQ1 q1 q2 EQ2 .
rewrite /regexEq in EQ1, EQ2.
move => l.
split => /= H /=.
+ inversion H. subst. constructor; firstorder.
+ inversion H. subst. constructor; firstorder.
Qed.

Global Instance regexEq_RAlt_m:  Proper (regexEq ==> regexEq ==> regexEq) RAlt.
Proof. move => p1 p2 EQ1 q1 q2 EQ2 .
move => l.
split => /= H /=. inversion H; subst.
apply rinterp_RAlt1. firstorder.
apply rinterp_RAlt2. firstorder.
inversion H; subst.
apply rinterp_RAlt1. firstorder.
apply rinterp_RAlt2. firstorder.
Qed.

Global Instance regexEq_rinterp_m: Proper (regexEq ==> eq ==> iff) rinterp.
Proof. move => r1 r2 EQ l1 l2 ->.
rewrite /regexEq in EQ. firstorder.
Qed.

Lemma regexEq_RSeqREmp r : RSeq r REmp === r.
Proof. rewrite /regexEq => l. rewrite rinterpRSeq. simpl (rinterp REmp). simpl.
split => //.  move => [l1 [l2 [H1 [H2 H3]]]]. subst. inversion H3; subst. by rewrite cats0.
move => H. exists l, nil. rewrite cats0. firstorder. constructor. Qed.

Lemma regexEq_REmpRSeq r : RSeq REmp r === r.
Proof. rewrite /regexEq => l. rewrite rinterpRSeq. simpl (rinterp REmp). simpl.
split => //.  move => [l1 [l2 [H1 [H2 H3]]]]. subst. inversion H2; subst. done.
move => H. exists nil, l. firstorder. constructor. Qed.

Lemma regexEq_RSeqRVoid r : RSeq r RVoid === RVoid.
Proof. rewrite /regexEq => l. rewrite rinterpRSeq. split => //.
move => [l1 [l2 [H1 [H2 H3]]]]. inversion H3. move => H. inversion H.
Qed.

Lemma regexEq_RVoidRSeq r : RSeq RVoid r === RVoid.
Proof. rewrite /regexEq => l. rewrite rinterpRSeq. split => //.
move => [l1 [l2 [H1 [H2 H3]]]]. inversion H2. move => H. inversion H.
Qed.

Lemma regexEq_RAltRVoid r : RAlt r RVoid === r.
Proof. rewrite /regexEq => l. rewrite rinterpRAlt. firstorder. inversion H. Qed.

Lemma regexEq_RVoidRAlt r : RAlt RVoid r === r.
Proof. rewrite /regexEq => l. rewrite rinterpRAlt. firstorder. inversion H. Qed.

Lemma regexEq_RSeqAssoc r1 r2 r3 : RSeq r1 (RSeq r2 r3) === RSeq (RSeq r1 r2) r3.
Proof. rewrite /regexEq => l. rewrite !rinterpRSeq. split.
+ move => [l1 [l2 [H1 [H2 H3]]]]. rewrite -> rinterpRSeq in H3.
destruct H3 as [l3 [l4 [H4 [H5 H6]]]]. subst. exists (l1++l3), l4. rewrite catA.
firstorder. by constructor.
+ move => [l1 [l2 [H1 [H2 H3]]]]. rewrite -> rinterpRSeq in H2.
destruct H2 as [l3 [l4 [H4 [H5 H6]]]]. subst. exists l3, (l4++l2). rewrite catA.
firstorder. by constructor.
Qed.

Lemma regexEq_RAltAssoc r1 r2 r3 : RAlt r1 (RAlt r2 r3) === RAlt (RAlt r1 r2) r3.
Proof. rewrite /regexEq => l. rewrite !rinterpRAlt. firstorder. Qed.

Lemma regexEq_RAltComm r1 r2 : RAlt r1 r2 === RAlt r2 r1.
Proof. rewrite /regexEq => l. rewrite !rinterpRAlt. firstorder. Qed.

Lemma regexEq_RStarVoid : RStar RVoid === REmp.
Proof. move => l. autorewrite with rinterp. destruct l => //.
split => // H. destruct H as [l1 [l2 [H1 [H2 H3]]]]. by rewrite -> rinterpRVoid in H2.
Qed.

Lemma regexEq_RStarEmp : RStar REmp === REmp.
Proof. move => l. autorewrite with rinterp. destruct l => //.
split => // H. destruct H as [l1 [l2 [H1 [H2 H3]]]]. subst.
by rewrite -> rinterpREmp in H2.
Qed.

(*
Lemma regexEq_RStarRStar r : RStar (RStar r) === RStar r.
Proof. induction r => l; autorewrite with rinterp.
+ destruct l => //.
split => H. destruct H as [l1 [l2 [H1 [H2 H3]]]]. subst.
rewrite -> rinterpRStar in H2.
destruct H2 as [l3 [l4 [H4 [H5 H6]]]]. subst.
rewrite -catA. exists l3, (l4 ++ l2).
*)

Lemma rSeqDef r1 : forall r2, rSeq r1 r2 === RSeq r1 r2.
Proof. induction r1 => r2.
(* RAny *)
+ destruct r2 => //.
  - by rewrite regexEq_RSeqREmp.
  - by rewrite regexEq_RSeqRVoid.
(* RSym *)
+ destruct r2 => //.
  - by rewrite regexEq_RSeqREmp.
  - by rewrite regexEq_RSeqRVoid.
(* REmp *)
+ rewrite regexEq_REmpRSeq. by destruct r2 => //.
(* RVoid *)
+ rewrite regexEq_RVoidRSeq. by destruct r2 => //.
(* RSeq *)
+ destruct r2 => //.
  - by rewrite /= -regexEq_RSeqAssoc IHr1_2.
  - by rewrite /= -regexEq_RSeqAssoc IHr1_2.
  - by rewrite -regexEq_RSeqAssoc regexEq_RSeqREmp.
  - by rewrite regexEq_RSeqRVoid.
  - by rewrite /= IHr1_2 regexEq_RSeqAssoc.
  - by rewrite /= IHr1_2 regexEq_RSeqAssoc.
  - by rewrite /= IHr1_2 regexEq_RSeqAssoc.
(* RAlt *)
+ destruct r2 => //.
  - by rewrite regexEq_RSeqREmp.
  - by rewrite regexEq_RSeqRVoid.
(* RStar *)
+ destruct r2 => //.
  - by rewrite regexEq_RSeqREmp.
  - by rewrite regexEq_RSeqRVoid.
Qed.

Lemma rAltDef r1 r2 : rAlt r1 r2 === RAlt r1 r2.
Proof. induction r1 => //=.
+ destruct r2 => //. by rewrite regexEq_RAltRVoid.
+ destruct r2 => //. by rewrite regexEq_RAltRVoid.
+ destruct r2 => //. by rewrite regexEq_RAltRVoid.
+ rewrite regexEq_RVoidRAlt. by destruct r2.
+ destruct r2 => //. by rewrite regexEq_RAltRVoid.
+ destruct r2 => //.
  - by rewrite IHr1_2 regexEq_RAltAssoc.
  - by rewrite IHr1_2 regexEq_RAltAssoc.
  - by rewrite IHr1_2 regexEq_RAltAssoc.
  - by rewrite regexEq_RAltRVoid.
  - by rewrite IHr1_2 regexEq_RAltAssoc.
  - by rewrite IHr1_2 regexEq_RAltAssoc.
  - by rewrite IHr1_2 regexEq_RAltAssoc.
+ destruct r2 => //.
  - by rewrite regexEq_RAltRVoid.
Qed.


(*======================================================================================
  Derivatives
  ======================================================================================*)

(* Nullable transformation *)
Fixpoint rnull (r: Regex) : Regex :=
match r with
| REmp     => REmp
| RAlt c1 c2 => rAlt (rnull c1) (rnull c2)
| RSeq c1 c2 => rSeq (rnull c1) (rnull c2)
| RStar c => REmp
| _ => RVoid
end.

Fixpoint rnullable (r: Regex) : bool :=
match r with
| REmp | RStar _ => true
| RAlt r1 r2 => rnullable r1 || rnullable r2
| RSeq r1 r2 => rnullable r1 && rnullable r2
| _ => false
end.

(* Derivative of a regexp wrt a symbol *)
Fixpoint rderivSym (s:sym) (r: Regex) : Regex :=
match r with
| RAny     => REmp
| RSym b   => if b==s then REmp else RVoid
| RAlt c d => rAlt (rderivSym s c) (rderivSym s d)
| RSeq c1 c2 => rAlt (rSeq (rderivSym s c1) c2) (rSeq (rnull c1) (rderivSym s c2))
| RStar r => rSeq (rderivSym s r) (RStar r)
| _ => RVoid
end.

(* Partial Antimirov-style derivative wrt a symbol *)
Definition nilRegexes: seq Regex := nil.
Definition singletonRegex r: seq Regex := [::r].
Definition unionRegexes s1 s2: seq Regex := s1 ++ s2.

Fixpoint arderivSym (s:sym) (r: Regex) : seq Regex :=
match r with
| RAny     => singletonRegex REmp
| RSym b   => if b==s then singletonRegex REmp else nilRegexes
| RAlt c d => unionRegexes (arderivSym s c) (arderivSym s d)
| RSeq r1 r2 => unionRegexes (map (fun r1' => RSeq r1' r2) (arderivSym s r1))
                             (if rnullable r1 then arderivSym s r2 else nilRegexes)
| RStar r => map (fun r' => RSeq r' (RStar r)) (arderivSym s r)
| _ => nilRegexes
end.

(* Generalization to strings *)
Fixpoint rderivSyms (ss: seq sym) r :=
if ss is s::ss' then rderivSyms ss' (rderivSym s r) else r.

Inductive matches : Regex -> seq sym -> Prop :=
| matchesEmp r : rinterp r nil -> matches r nil
| matchesCons r a s : matches (rderivSym a r) s -> matches r (a::s).


(* Semantic interpretation of nullable *)
Lemma rinterpNull r : forall l, rinterp (rnull r) l <-> (l = nil /\ rinterp r nil).
Proof. induction r => l/=; autorewrite with rinterp.
+ split => //. move => [H1 H2]. by destruct H2.
+ split => //. by move => [H1 H2].
+ intuition.
+ intuition.
+ rewrite rSeqDef. autorewrite with rinterp.
split.
move => H. destruct H as [l1 [l2 [H1 [H2 H3]]]]. subst.
destruct (proj1 (IHr1 _) H2) as [H4 H5]. subst.
destruct (proj1 (IHr2 _) H3) as [H6 H7]. subst.
split => //. exists nil, nil. intuition.
move => [H [l1 [l2 [H3 [H4 H5]]]]].
subst. exists l1, l2. split => //.
split. destruct l1 => //.  destruct l2 => //.
specialize (IHr1 nil). destruct IHr1 as [I1 I2]. apply I2. intuition.
specialize (IHr2 nil). destruct IHr2 as [I1 I2]. destruct l1 => //. destruct l2 => //.
apply I2. intuition.
+ rewrite rAltDef. autorewrite with rinterp.
split. move => H. destruct H.
+ destruct (proj1 (IHr1 _) H) as [H1 H2]. intuition.
+ destruct (proj1 (IHr2 _) H) as [H1 H2]. intuition.
move => [H1 H2].
subst. destruct H2.
+ specialize (IHr1 nil). left. by apply (proj2 IHr1).
+ specialize (IHr2 nil). right. by apply (proj2 IHr2).
+ intuition.
Qed.


(* Semantic interpretation of rderivSym *)
Lemma rinterpDerivSym c r : forall s, rinterp (rderivSym c r) s <-> rinterp r (c::s).
Proof. induction r => s; autorewrite with rinterp.
(* RAny *)
split => //=. move => ->. by exists c. move => [b H]. congruence.
(* RSym *)
split => //=.
case E: (sym0 == c). rewrite rinterpREmp. move => ->. by rewrite (eqP E).
by rewrite rinterpRVoid.
case E: (sym0 == c). rewrite rinterpREmp. rewrite (eqP E). by move => /=[H].
move => [H]/=. by rewrite H eq_refl in E.
(* REmp *)
split => //=.
(* RVoid *)
done.
(* RSeq *)
+ rewrite /= rAltDef 2!rSeqDef rinterpRAlt !rinterpRSeq. split => //= H.
(* => *)
destruct H.
-
destruct H as [l1 [l2 [H1 [H2 H3]]]].
exists (c::l1), l2. split. by subst. split => //.
by apply (IHr1 _).
-
destruct H as [l1 [l2 [H1 [H2 H3]]]]. subst.
apply rinterpNull in H2. destruct H2 as [H4 H5]. subst.
simpl. exists nil, (c::l2). split => //. split => //.
by apply (IHr2 l2).
(* <= *)
destruct H as [l1 [l2 [H1 [H2 H3]]]].
case E: l1 => [| c' l3].
-
subst. simpl in H1. subst.
right.
specialize (IHr2 s).
destruct IHr2 as [I1 I2]. specialize (I2 H3). exists nil, s. split => //. split => //.
by apply rinterpNull.
-
subst. injection H1 => [H4 H5]. subst. clear H1.
specialize (IHr1 l3). destruct IHr1 as [I1 I2].
specialize (I2 H2). left.
exists l3,l2. split => //.
(* RAlt *)
rewrite /= rAltDef !rinterpRAlt.
split => //= H.
(* => *)
destruct H.
left. by apply IHr1.
right. by apply IHr2.
(* <= *)
destruct H.
left. by apply IHr1.
right. by apply IHr2.
(* RStar *)
rewrite /= rSeqDef rinterpRSeq.
firstorder.
Qed.

Lemma rinterpDerivSyms s: forall r l, rinterp (rderivSyms s r) l <-> rinterp r (s++l).
Proof. induction s => //= r l. by rewrite IHs rinterpDerivSym. Qed.

Global Instance regexEq_rderivSym_m c :
  Proper (regexEq ==> regexEq) (rderivSym c).
Proof. move => r1 r2 EQ l. by rewrite 2!rinterpDerivSym EQ. Qed.

Fixpoint starfree (r: Regex) :=
match r with
| RAlt r s => starfree r && starfree s
| RSeq r s => starfree r && starfree s
| RStar _ => false
| _ => true
end.

(* r is expected to be star-free *)
Fixpoint DrvAny (r: Regex) :=
match r with
| REmp     => RVoid
| RSym b   => REmp
| RAny     => REmp
| RVoid    => RVoid
| RAlt c1 c2 => rAlt (DrvAny c1) (DrvAny c2)
| RSeq c1 c2 => rAlt (rSeq (DrvAny c1) c2) (rSeq (rnull c1) (DrvAny c2))
| RStar c => RVoid
end.

(* Derivative of a regexp g wrt another regexp r *)
Fixpoint deriv (r: Regex) g :=
match r with
| REmp     => g
| RSym b   => rderivSym b g
| RAny     => DrvAny g
| RVoid    => RVoid
| RAlt c1 c2 => rAlt (deriv c1 g) (deriv c2 g)
| RSeq c1 c2 => deriv c2 (deriv c1 g)
| RStar c => RVoid
end.

Lemma starfreerSeq r1 r2 : starfree r1 -> starfree r2 -> starfree (rSeq r1 r2).
Proof. move => SF1 SF2. induction r1 => //=. destruct r2 => //;destruct r2 => //.
destruct r2 => //; destruct r2 => //. destruct r2 => //. destruct r2 => //=.
simpl in SF1. destruct (andP SF1) as [SF1a SF1b]. destruct r2 => //=.
rewrite IHr1_2 => //. by rewrite SF1a. rewrite SF1a. rewrite IHr1_2 => //.
rewrite SF1a. rewrite IHr1_2 => //. rewrite SF1a. rewrite IHr1_2 => //.
simpl in SF1. destruct (andP SF1) as [SF1a SF1b]. destruct r2 => //=.
rewrite SF1a. by rewrite SF1b.
rewrite SF1a. by rewrite SF1b.
simpl in SF2. destruct (andP SF2) as [SF2a SF2b].
by rewrite SF1a SF1b SF2a SF2b.
simpl in SF2. destruct (andP SF2) as [SF2a SF2b].
by rewrite SF1a SF1b SF2a SF2b.
Qed.

Lemma starfreerAlt r1 r2 : starfree r1 -> starfree r2 -> starfree (rAlt r1 r2).
Proof. move => SF1 SF2. induction r1 => //=.
destruct r2 => //; destruct r2 => //.
destruct r2 => //; destruct r2 => //.
destruct r2 => //; destruct r2 => //.
destruct r2 => //; destruct r2 => //.
simpl in SF1. destruct (andP SF1) as [SF1a SF1b]. destruct r2 => //=.
by rewrite SF1a SF1b.
by rewrite SF1a SF1b.
by rewrite SF1a SF1b.
simpl in SF2. destruct (andP SF2) as [SF2a SF2b].
by rewrite SF1a SF1b SF2a SF2b.
simpl in SF2. destruct (andP SF2) as [SF2a SF2b].
by rewrite SF1a SF1b SF2a SF2b.
destruct r2 => //=.
simpl in SF1. destruct (andP SF1) as [SF1a SF1b].
rewrite SF1a. rewrite IHr1_2 => //.
simpl in SF1. destruct (andP SF1) as [SF1a SF1b].
rewrite SF1a. rewrite IHr1_2 => //.
simpl in SF1. destruct (andP SF1) as [SF1a SF1b].
rewrite SF1a. rewrite IHr1_2 => //.
simpl in SF1. destruct (andP SF1) as [SF1a SF1b].
simpl in SF2. destruct (andP SF2) as [SF2a SF2b].
rewrite SF1a. rewrite IHr1_2 => //.
simpl in SF1. destruct (andP SF1) as [SF1a SF1b].
rewrite SF1a. rewrite IHr1_2 => //.
Qed.

Lemma starfreeNull r : starfree r -> starfree (rnull r).
Proof. induction r => //=. move/andP => [R1 R2].
rewrite starfreerSeq => //. rewrite IHr1 => //.
rewrite IHr2 => //.
move/andP => [R1 R2].
rewrite starfreerAlt => //. rewrite IHr1 => //. rewrite IHr2 => //.
Qed.

Lemma starfreeDrvAny r : starfree r -> starfree (DrvAny r).
Proof. induction r => //=. move/andP => [R1 R2].
apply starfreerAlt => //. apply starfreerSeq => //. apply IHr1 => //.
apply starfreerSeq => //. apply starfreeNull => //.
apply IHr2 => //.
move/andP => [R1 R2].
apply starfreerAlt. apply IHr1 => //. apply IHr2 => //.
Qed.

Lemma starfreeDerivSym r : forall c, starfree r -> starfree (rderivSym c r).
Proof. induction r => //= c R.
by destruct (sym0 == c).
destruct (andP R) as [R1 R2].
apply starfreerAlt => //. apply starfreerSeq => //. apply IHr1 => //.
apply starfreerSeq => //. apply starfreeNull => //. apply IHr2 => //.
destruct (andP R) as [R1 R2].
apply starfreerAlt => //. apply IHr1 => //. apply IHr2 => //.
Qed.

Lemma starfreeDeriv r1 : forall r2, starfree r1 -> starfree r2 -> starfree (deriv r1 r2).
Proof. induction r1 => //=.
destruct r2 => //=.
move => _. move/andP => [R1 R2].
rewrite starfreerAlt => //. rewrite starfreerSeq => //. apply starfreeDrvAny => //.
rewrite starfreerSeq => //. apply starfreeNull => //. apply starfreeDrvAny => //.
move => _. move/andP => [R1 R2].
rewrite starfreerAlt => //. apply starfreeDrvAny => //. apply starfreeDrvAny => //.
move => r _ R. apply starfreeDerivSym => //.
move => r2. move/andP => [R1 R2] R3. apply IHr1_2 => //.
apply IHr1_1 => //.
move => r2. move/andP => [R1 R2] R3. apply starfreerAlt.
apply IHr1_1 => //.
apply IHr1_2 => //.
Qed.

(* Semantic definition of non-overlapping *)
Definition nonOverlapping r1 r2 := forall l1 l2, rinterp r1 l1 -> rinterp r2 (l1++l2) -> False.

(* This syntactic criterion implies a sensible semantic one *)
Definition NonOverlapping r1 r2 := match deriv r1 r2 with RVoid => true | _ => false end.

Fixpoint req (r1 r2: Regex) :bool :=
  match r1, r2 with
  | RAny, RAny => true
  | RSym s1, RSym s2 => s1==s2
  | RVoid, RVoid => true
  | REmp, REmp => true
  | RSeq r1a r1b, RSeq r2a r2b => req r1a r2a && req r1b r2b
  | RAlt r1a r1b, RAlt r2a r2b => req r1a r2a && req r1b r2b
  | RStar r1, RStar r2 => req r1 r2
  | _, _ => false
  end.

Definition States := seq Regex.
Fixpoint tryLookupState (ss: States) (r: Regex) :=
  if ss is r'::ss' then
    if req r r' then Some (size ss') else tryLookupState ss' r
  else None.

Definition lookupState (ss: States) (r: Regex) : States * nat :=
  if tryLookupState ss r is Some i then (ss, i)
  else (r::ss, size ss).

End Regex.

Fixpoint explore n (r: Regex bool_eqType) (ss: States _) (t: seq (nat*nat*nat)) :=
  if tryLookupState ss r is Some i then (ss,t,i)
  else
    let ss' := r::ss in
    let i := size ss in

    if n isn't n.+1 then (ss', t, i)
    else
    (* Derivatives wrt 0 and 1 symbols *)
      let r0 := rderivSym false r in
      let r1 := rderivSym true r in
      let: (ss0, t0, i0) := explore n r0 ss' t in
      let: (ss1, t1, i1) := explore n r1 ss0 t0 in
      (ss1, (i,i0,i1)::t1, i).

Definition iterations := 100.
Definition MAKEDFA r := explore iterations r nil nil.

Example r := RSeq (RStar (RSeq (RSym false) (RSym true))) (RSym true).

Compute MAKEDFA r.

(* Semantic interpretation of DrvAny *)
Lemma rinterpDrvAny r : starfree r -> forall l,
  rinterp (DrvAny r) l <-> exists b:bool, rinterp r (b::l).
Proof. move => SF.
induction r => l/=.
+ rewrite rinterpREmp. split => H. subst. exists true. rewrite rinterpRAny. by exists true.
  destruct H as [b H]. rewrite -> rinterpRAny in H. destruct H as [b2 H]. congruence.
+ rewrite rinterpREmp. split => H. subst. exists sym. by rewrite rinterpRSym.
  destruct H as [b H]. rewrite -> rinterpRSym in H. congruence.
+ split => //. rewrite rinterpRVoid. by move => [b H].
  move => [b H]. by rewrite -> rinterpREmp in H.
+ split => //. rewrite rinterpRVoid. by move => [_ H].
  move => [b H]. by rewrite -> rinterpRVoid in H.
+ rewrite rAltDef !rSeqDef rinterpRAlt 2!rinterpRSeq.
  simpl in SF. destruct (andP SF) as [SF1 SF2].
  split => // H. destruct H.
  - destruct H as [l1 [l2 [H1 [H2 H3]]]]. subst.
    destruct (proj1 (IHr1 SF1 _) H2) as [b H4]. exists b. rewrite rinterpRSeq.
    exists (b::l1), l2. intuition.
    destruct H as [l1 [l2 [H1 [H2 H3]]]]. subst. rewrite -> rinterpNull in H2.
    destruct H2 as [H4 H5]. subst. simpl.
    destruct (proj1 (IHr2 SF2 _) H3) as [b H4]. exists b. rewrite rinterpRSeq.
    exists nil, (b::l2). intuition.
  - destruct H as [b H]. rewrite ->rinterpRSeq in H.
    destruct H as [l1 [l2 [H1 [H2 H3]]]].
    destruct l1.
    - right. exists nil, l. split => //. rewrite rinterpNull. split => //.
      rewrite (IHr2 SF2). simpl in H1. subst. by exists b.
    - left. inversion H1. subst. exists l1, l2. split => //.
      rewrite (IHr1 SF1). split => //. by exists s.
+ simpl in SF. destruct (andP SF) as [SF1 SF2].
rewrite rAltDef rinterpRAlt. rewrite (IHr1 SF1) (IHr2 SF2).
split => //. move => H. destruct H; destruct H as [b H]; exists b. by apply rinterp_RAlt1.
by apply rinterp_RAlt2. move => [b H]. rewrite -> rinterpRAlt in H. firstorder.
by simpl in SF.
Qed.

(* Semantic interpretation of deriv *)
Lemma rinterpDeriv (r2:Regex bool_eqType) : forall r1 s2, starfree r1 -> starfree r2 -> (rinterp (deriv r2 r1) s2 <-> exists s1, rinterp r2 s1 /\ rinterp r1 (s1 ++ s2)).
Proof. induction r2 => r1 l1 SF1 SF2 //=.
+ rewrite rinterpDrvAny. split => H. destruct H as [b H]. exists [::b].
  rewrite rinterpRAny. split => //.  by exists b.
  destruct H as [l2 H]. rewrite -> rinterpRAny in H. destruct H as [[b H1] H2].
  subst. by exists b. done.
+ rewrite -> rinterpDerivSym. split => H. eexists [::sym].
  rewrite rinterpRSym. by intuition.
+ destruct H as [s1 [H1 H2]]. rewrite -> rinterpRSym in H1. by subst.
+ split => H. exists nil. rewrite rinterpREmp. done.
+ destruct H as [s1 [H1 H2]]. rewrite -> rinterpREmp in H1. by subst.
+ split => // H. by rewrite -> rinterpRVoid in H.
  destruct H as [s1 [H1 H2]]. by rewrite -> rinterpRVoid in H1.
+ simpl in SF2. destruct (andP SF2) as [SF2a SF2b]. rewrite IHr2_2 => //. split.
  move => [l1' [H1 H2]]. specialize (IHr2_1 r1 (l1'++l1) SF1 SF2a).
  rewrite -> IHr2_1 in H2.
  destruct H2 as [l3 [H3 H4]]. exists (l3++l1'). rewrite -catA.  split => //.
  rewrite rinterpRSeq. exists l3, l1'. intuition.
  move => [l1' [H1 H2]]. rewrite -> rinterpRSeq in H1.
  destruct H1 as [l3 [l4 [H3 [H4 H5]]]]. subst.
  exists l4. split => //.
  apply IHr2_1 => //.
  exists l3. rewrite catA. intuition. apply starfreeDeriv => //.
+ simpl in SF2. destruct (andP SF2) as [SF2a SF2b].
  rewrite rAltDef rinterpRAlt. rewrite (IHr2_2 _ _ SF1 SF2b). rewrite (IHr2_1 _ _ SF1 SF2a).
  split => H. destruct H. destruct H as [s1 [H1 H2]]. exists s1. rewrite rinterpRAlt.
  intuition.
  destruct H as [s1 [H1 H2]]. exists s1. rewrite rinterpRAlt. intuition.
  destruct H as [l1' [H1 H2]].
  rewrite -> rinterpRAlt in H1. destruct H1. left. by exists l1'. right. by exists l1'.
Qed.

(*
Corollary regexEq_deriv_m :
  Proper (@regexEq _ ==> @regexEq _ ==> @regexEq _) (@deriv bool_eqType).
Proof. rewrite /regexEq. move => r1 r2 /=EQ q1 q2 /=EQ' l.
split. rewrite -> rinterpDeriv. move => [l' [H1 H2]]. rewrite rinterpDeriv.
exists l'.  rewrite -EQ' -EQ. intuition.
move => [l' [H1 H2]]. exists l'.
rewrite EQ' EQ. intuition.
Qed.

Lemma rinterpSeqSymDeriv (c:bool) r : forall l,
  rinterp (RSeq (RSym c) (rderivSym c r)) l <-> exists l', l = c::l' /\ rinterp r l.
Proof.
move => l. rewrite rinterpRSeq.  simpl (rinterp _ _).
split.
+ move => [l1 [l2 [H1 [H2 H3]]]]. subst. rewrite -> rinterpDerivSym in H3. by exists l2.
+ move => [l' [H1 H2]]. subst. exists [::c], l'. by rewrite rinterpDerivSym.
Qed.
*)

Lemma NonOverlappingSound (r1 r2: Regex bool_eqType) : starfree r1 -> starfree r2 -> NonOverlapping r1 r2 -> nonOverlapping r1 r2.
Proof. rewrite /NonOverlapping/nonOverlapping. move => SF1 SF2 H l1 l2 R1 R2.
case E1: (deriv r1 r2); rewrite E1 in H => //.
have RDR := @rinterpDeriv r1 r2 l2 SF2 SF1. rewrite E1/= in RDR.
destruct RDR as [_ R].
rewrite -> rinterpRVoid in R. destruct R.
by exists l1.
Qed.

Definition onestep (r: Regex _) :=
  rAlt (rnull r) (
  rAlt (rSeq (RSym false) (rderivSym false r))
       (rSeq (RSym true) (rderivSym true r))).

Notation "x '===' y" := (regexEq x y) (at level 70, no associativity).

(*
Lemma rinterpOnestep r : onestep r === r.
Proof. rewrite /onestep. rewrite !rAltDef !rSeqDef. elim.
simpl. split => H. destruct H. apply rinterpNull in H. intuition.
destruct H. destruct H as [l1 [l2 [H1 [H2 H3]]]]. by subst.
destruct H as [l1 [l2 [H1 [H2 H3]]]]. by subst.
left.
apply rinterpNull.  intuition.

move => a l.
rewrite !rinterpRAlt !rinterpNull !rinterpSeqSymDeriv.
move => [H1 H2]. split.
move => H'. destruct H'. by destruct H.
destruct H; firstorder.
move => H3.
right. destruct a. - right. by exists l. - left. by exists l.
Qed.

*)

