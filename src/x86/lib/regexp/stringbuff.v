Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple.
Require Import path fingraph  finset.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr x86proved.monad reader writer procstate procstatemonad mem exn eval instrcodec
               monadinst ioaction bitsrep bitsops eval step pointsto cursor.
Require Import program programassem reg instrsyntax instrrules.
Require Import spectac iltac triple.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(****************************************************************)
(* C-style strings                                              *)
(****************************************************************)

Definition CString (s: seq DWORD) := all (fun x => x != #0) s.

Lemma snocCString
        (l1 : seq DWORD)(H: CString l1)
        (c : DWORD)(_ : c != #0):
  CString (l1 ++ [:: c]).
Proof.
  rewrite /CString.
  rewrite all_cat; apply /andP.
  split; first by rewrite /CString in H; exact: H.
  rewrite all_seq1.
  done.
Qed.

Lemma snocMem (lo pd: DWORD)(l1 : seq DWORD)(c: DWORD):
  pd :-> c ** lo -- pd :-> l1 |-- lo -- next (pd +# 3) :-> (cat l1 [:: c]).
Proof.
  rewrite ->seqMemIsCat.
  rewrite pairMemIsPair.
  apply lexistsR with (x := pd).
  rewrite ->seqMemIsCons.
  ssimpl. rewrite /pointsTo; apply lexistsL => q.
  rewrite -> memIsFixed. sdestruct => AP. sbazooka.
  rewrite ->seqMemIsNil. apply apart_addBn_next in AP.
 sbazooka.
Qed.

Lemma catCString (l1: seq DWORD) (H1: CString l1) l2 (H2: CString l2):
  CString (l1 ++ l2).
Proof.
   rewrite /CString.
   rewrite /CString in H1, H2.
   by rewrite all_cat H1 H2.
Qed.

Definition memToS {R} {_:MemIs R} p q (s: seq DWORD) :=
    CString s
/\\ p -- q :-> s
 ** q :-> (#0: DWORD).

Definition pointsToS {R} {_:MemIs R} p (s: seq DWORD) :=
  Exists q: DWORD, memToS p q s.

Notation "p '--' q ':-S>' x" := (memToS p q x)
    (at level 50, q at next level,  no associativity).
Notation "p ':-S>' x" := (pointsToS p x)
    (at level 50,  no associativity).

Lemma caseString_nil (q r: DWORD):
  q -- r :-S> [::] |-- q == r /\\ r :-> (#0: DWORD).
Proof.
  rewrite /memToS [CString _]/= /cat; sdestruct=> _.
  rewrite seqMemIsNil.
  sdestruct=> /eqP eq.
  sbazooka.
Qed.

Lemma caseString_cons (q r: DWORD)(c: DWORD)(cs: seq DWORD) :
  q -- r :-S> [:: c & cs] |-- (c != #0) /\\ q :-> c ** next (q +# 3) -- r :-S> cs.
Proof.
  rewrite /memToS.
  rewrite /CString /all-/all.
  rewrite seqMemIsCons.
  sdestruct=> /andP [cn0 cstr].
  sdestruct=> q'.
  ssplit.
    * exact: cn0.
    * sbazooka.
      rewrite ->memIsFixed; sdestruct=> H. apply apart_addBn_next in H. rewrite H.
      rewrite /pointsTo.
      sbazooka.
Qed.

Lemma splitString (q r: DWORD)(l2: seq DWORD):
     q -- r :-S> l2
 |--   ((l2 == [::]) && (q == r) /\\ q :-> (#0: DWORD))
  \\// (Exists c: DWORD, Exists cs: seq DWORD,
        ((l2 == [:: c & cs])
      && (c != (#0: DWORD))
      /\\ q :-> c ** next (q +# 3) -- r :-S>  cs)).
Proof.
  case: l2.
  * (* CASE: l2 =~ [::] *)
    apply lorR1.
    rewrite ->caseString_nil.
    sdestruct=> /eqP <-.
    sbazooka.
    by apply /andP; split; done.

  * (* CASE: l2 =~ [:: c & cs ] *)
    move=> c cs.
    apply lorR2.
    apply lexistsR with (x := c);
      apply lexistsR with (x := cs).
    rewrite ->caseString_cons.
    sbazooka.
    by apply /andP; split; done.
Qed.

Lemma emptyString (lo hi: DWORD)(l: seq DWORD)(_ : CString l):
  hi :-> (#0: DWORD) ** lo -- hi :-> l  |-- lo -- hi :-S> l.
Proof.
  rewrite /memToS.
  ssplit; first by done.
  sbazooka.
Qed.


Lemma catString (lo hi pd: DWORD)(l1 l2: seq DWORD)(_: CString l1):
  lo -- pd :-> l1 ** pd -- hi :-S> l2
     |-- lo -- hi :-S> (cat l1 l2).
Proof.
  rewrite /memToS.
  rewrite ->seqMemIsCat. rewrite pairMemIsPair.
  sdestruct=> l2IsString; ssplit; last by sbazooka.
  rewrite /CString.
  rewrite all_cat; apply /andP; split; by exact.
Qed.

Lemma memIsNextS (p q q' : DWORD) l : next p = mkCursor q' ->
  next p -- q :-S> l |-- p+#1 -- q :-S> l.
Proof. move => H0.
destruct l.
+ rewrite /memToS !seqMemIsNil.
  sdestructs => H H'. sbazooka. by rewrite (nextIsInc H').
+ rewrite /memToS !seqMemIsCons.
  sdestructs => H H'. sbazooka. have H1 := nextIsInc H0. by  rewrite H0 -H1.
Qed.