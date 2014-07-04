(*===========================================================================
    Macro for multiplication by a constant
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.spectac x86proved.opred x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.basic x86proved.x86.macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Generate a sequence that computes r1 + r2*m with result in r1 and r2 trashed *)
Open Scope instr_scope.
(*=add_mulc *)
Fixpoint add_mulc nbits (r1 r2: Reg) (m: nat) :=
  if nbits is nbits'.+1
  then if odd m
       then ADD r1, r2;; SHL r2, 1;; add_mulc nbits' r1 r2 m./2
       else SHL r2, 1;;              add_mulc nbits' r1 r2 m./2
  else prog_skip.
(*=End *)

(*=add_mulcCorrect *)
Lemma add_mulcCorrect nbits : forall (r1 r2: Reg) m, m < 2^nbits ->
  |-- Forall v, Forall w,
      basic
      (r1 ~= v ** r2 ~= w ** OSZCP?)
      (add_mulc nbits r1 r2 m) empOP
      (r1 ~= addB v (mulB w (fromNat m)) ** r2? ** OSZCP?).
(*=End *)
Proof.
  induction nbits => r1 r2 m LT; rewrite /add_mulc; fold add_mulc; specintros => v w.

  (* nbits = 0 *)
  destruct m => //. autorewrite with bitsHints push_at.
  apply: basic_roc_post; last apply basic_skip.
  rewrite /stateIsAny. sbazooka.

  (* nbits != 0 *)
  have H: m./2 < 2 ^nbits.
  rewrite expnS mul2n in LT.
  rewrite -(odd_double_half m) in LT.
  rewrite -ltn_double.
  apply (ltn_addl (odd m)) in LT.
  by rewrite -(ltn_add2l (odd m)).

  autorewrite with push_at.

  case ODD: (odd m).

(* lsb is 1 *)
  (* ADD r1, r2 *)
  basicapply ADD_RR_ruleNoFlags.
  basicapply SHL_RI_rule => //.
  try_basicapply IHnbits => //.

  rewrite /iter -addBA shlB_asMul -mulB_muln mul2n.
  rewrite -{2}(odd_double_half m).
  by rewrite ODD mulB_addn mulB1.

  basicapply SHL_RI_rule => //.
  try_basicapply IHnbits => //.

  by rewrite /iter shlB_asMul -mulB_muln mul2n -{2}(odd_double_half m) ODD add0n.
Qed.


(* More efficient version that does multi-bit shifts *)
Fixpoint add_mulcAux nbits (c:nat) (r1 r2: Reg) (m: nat) : program :=
  (if nbits is nbits'.+1
  then if odd m
       then
         if c == 0
         then ADD r1, r2;; add_mulcAux nbits' 1 r1 r2 m./2
         else SHL r2, c;; ADD r1, r2;; add_mulcAux nbits' 1 r1 r2 m./2
       else add_mulcAux nbits' c.+1 r1 r2 m./2
  else prog_skip)%asm.

Lemma add_mulcAuxCorrect nbits : forall (c:nat) (r1 r2: Reg) (m:nat),
  c+nbits <= 32 ->
  m < 2^nbits ->
  |-- Forall v, Forall w,
  basic
  (r1 ~= v ** r2 ~= w)
  (add_mulcAux nbits c r1 r2 m) empOP
  (r1 ~= addB v (w *# (m*2^c)) ** r2?) @ OSZCP?.
Proof.
  induction nbits => c r1 r2 m LT1 LT3;
  rewrite /add_mulcAux; fold add_mulcAux; specintros => v w.

  (* nbits = 0 *)
  destruct m => //. autorewrite with bitsHints push_at.
  apply: basic_roc_post; last apply basic_skip.
  rewrite /stateIsAny. sbazooka.

  (* nbits != 0 *)
  have H: m./2 < 2 ^nbits.
  rewrite expnS mul2n in LT3.
  rewrite -(odd_double_half m) in LT3.
  rewrite -ltn_double.
  apply (ltn_addl (odd m)) in LT3.
  by rewrite -(ltn_add2l (odd m)).

  autorewrite with push_at.

  case ODD: (odd m).

(* lsb is 1 *)

  case ZERO: (c == 0).
  (* c is 0 *)

  (* ADD r1, r2 *)
  basicapply ADD_RR_ruleNoFlags.

  basicapply IHnbits => //.
  rewrite (eqP ZERO).  rewrite expn0 muln1 expn1.
  rewrite muln2. rewrite -{2}(odd_double_half m) ODD.  rewrite mulB_addn mulB1. rewrite -> addBA.
  sbazooka.

  rewrite (eqP ZERO) add0n in LT1. by rewrite add1n.

  (* c is not 0 *)

  (* SHL r2, c *)
  basicapply SHL_RI_rule => //.

  (* ADD r1, r2 *)
  basicapply ADD_RR_ruleNoFlags.

  basicapply IHnbits => //.

  rewrite expn1 -{2}(odd_double_half m) ODD. rewrite muln2. rewrite -addBA.
  rewrite mulnDl mul1n. rewrite mulB_addn. rewrite mulnC.
  rewrite shlB_mul2exp mulB_muln. sbazooka.

  rewrite add1n. rewrite -addn1 addnA addn1 addnC in LT1.
  apply (ltn_addr c) in LT1. by rewrite -(ltn_add2r c).

  rewrite -(addn1) addnA addn1 in LT1.
  apply (ltn_addr nbits) in LT1. by rewrite -(ltn_add2r nbits).



(* lsb is 0 *)

  basicapply IHnbits => //.
  rewrite expnS.
  rewrite -{2}(odd_double_half m) ODD add0n.
  rewrite mulnA. rewrite muln2.
  sbazooka.
  by rewrite -(addn1 c) -addnA add1n.
Qed.

(* Now a peephole optimization, using LEA for special cases *)
Definition add_mulcOpt (r1 r2: NonSPReg) (m:nat) : program :=
  (if m == 2
  then LEA r1, [r1 + r2*2]
  else
  if m == 4
  then LEA r1, [r1 + r2*4]
  else
  if m == 8
  then LEA r1, [r1 + r2*8]
  else add_mulcAux 32 0 r1 r2 m)%asm.

Lemma add_mulcOptCorrect (r1 r2: NonSPReg) (m:nat):
  m < 2^32 ->
  |-- Forall v, Forall w,
  basic
  (r1 ~= v ** r2 ~= w)
  (add_mulcOpt r1 r2 m) empOP
  (r1 ~= addB v (w *# m) ** r2?) @ OSZCP?.
Proof.
rewrite /add_mulcOpt.
move => LT. specintros => v w.
autorewrite with push_at.

case EQ2: (m == 2).

basicapply LEA_ruleSameBase => //.
rewrite /eval.scaleBy shlB_asMul. rewrite -> addB0. rewrite /stateIsAny (eqP EQ2).
sbazooka.

case EQ4: (m == 4).

basicapply LEA_ruleSameBase => //.
rewrite /eval.scaleBy !shlB_asMul. rewrite -> addB0. rewrite /stateIsAny (eqP EQ4) -mulB_muln.
replace (2*2) with 4 by done. sbazooka.

case EQ8: (m == 8).
basicapply LEA_ruleSameBase => //.
rewrite /eval.scaleBy !shlB_asMul. rewrite -> addB0. rewrite /stateIsAny (eqP EQ8) -!mulB_muln.
replace (2*_) with 8 by done. sbazooka.

try_basicapply add_mulcAuxCorrect => //.
by rewrite expn0 muln1.
Qed.


(* More efficient version that does multi-bit shifts.
   Also with clever use of LEA where possible, iterated *)
(*=add_mulcFast *)
Fixpoint gen nb (c:nat) (r1:Reg) (r2: NonSPReg) m :=
  if nb is nb'.+1
  then if odd m then
    match c with
    | 0 => ADD r1, r2;;             gen nb' 1 r1 r2 m./2
    | 1 => LEA r1, [r1 + r2*2];;    gen nb' 2 r1 r2 m./2
    | 2 => LEA r1, [r1 + r2*4];;    gen nb' 3 r1 r2 m./2
    | 3 => LEA r1, [r1 + r2*8];;    gen nb' 4 r1 r2 m./2
    | _ => SHL r2, c;; ADD r1, r2;; gen nb' 1 r1 r2 m./2
    end else                        gen nb' c.+1 r1 r2 m./2
  else prog_skip.
Definition add_mulcFast (r1:Reg) (r2: NonSPReg) (d:DWORD) :=
  gen 32 0 r1 r2 (toNat d).
(*=End *)

Lemma genCorrect nbits : forall (c:nat) (r1:Reg) (r2:NonSPReg) (m:nat),
  c+nbits <= 32 ->
  m < 2^nbits ->
  |-- Forall v, Forall w,
  basic
  (r1 ~= v ** r2 ~= w)
  (gen nbits c r1 r2 m) empOP
  (r1 ~= addB v (w *# (m*2^c)) ** r2?) @ OSZCP?.
Proof.
  induction nbits => c r1 r2 m LT1 LT3;
  rewrite /gen; fold gen; specintros => v w.
  autorewrite with push_at.

  (* nbits = 0 *)
  destruct m => //. autorewrite with bitsHints.
  apply: basic_roc_post; last apply basic_skip.
  rewrite /stateIsAny. sbazooka.

  (* nbits != 0 *)
  have H: m./2 < 2 ^nbits.
  rewrite expnS mul2n in LT3.
  rewrite -(odd_double_half m) in LT3.
  rewrite -ltn_double.
  apply (ltn_addl (odd m)) in LT3.
  by rewrite -(ltn_add2l (odd m)).

  autorewrite with push_at.

  case ODD: (odd m).

(* lsb is 1 *)

  destruct c.
  (* c is 0 *)

  (* ADD r1, r2 *)

  basicapply ADD_RR_ruleNoFlags.

  try_basicapply IHnbits => //.
  rewrite expn0 muln1 expn1.
  rewrite muln2. rewrite -{2}(odd_double_half m) ODD. by rewrite mulB_addn mulB1; rewrite -> addBA.

  destruct c.

  (* c is 1 *)
  basicapply LEA_ruleSameBase.
  rewrite -> addB0. rewrite /eval.scaleBy shlB_asMul.

  try_basicapply IHnbits => //.
  rewrite expn1 -{2}(odd_double_half m) ODD. rewrite muln2. rewrite -addBA.
  replace (2^2) with (2*2) by done. rewrite mulnA. rewrite -mulB_addn. rewrite !muln2.
  rewrite -(odd_double_half m). by rewrite ODD mulB_addn.

  destruct c.

  (* c is 2 *)
  basicapply LEA_ruleSameBase.
  rewrite -> addB0. rewrite /eval.scaleBy shlB_asMul.

  try_basicapply IHnbits => //.
  rewrite shlB_asMul.
  rewrite -addBA. rewrite <-mulBA. rewrite <- (mulBDr w).
  rewrite 3!expnS expn0 muln1 mulnA.
  rewrite fromNat_mulBn. rewrite fromNat_addBn. rewrite mulnA. rewrite -mulnDl.
  replace (2+m./2 * 2 *2) with (true*2 + m./2 * 2 * 2) by done.
  rewrite -mulnDl.
  rewrite -ODD. rewrite !muln2. rewrite -> (odd_double_half m).
  rewrite -!muln2. by rewrite mulnA.

  destruct c.

  (* c is 3 *)
  basicapply LEA_ruleSameBase.
  rewrite -> addB0. rewrite /eval.scaleBy !shlB_asMul.

  try_basicapply IHnbits => //.
  rewrite -addBA. rewrite <-!mulBA. rewrite <- (mulBDr w).
  rewrite 4!expnS expn0 muln1 mulnA.
  rewrite 2!fromNat_mulBn. rewrite fromNat_addBn. rewrite 2!mulnA. rewrite -mulnDl.
  rewrite 2!mulnA.
  rewrite -mulnDl.
  replace (2+m./2 * 2 *2) with (true*2 + m./2 * 2 * 2) by done.
  rewrite -mulnDl.
  rewrite -ODD. rewrite !muln2. rewrite -> (odd_double_half m).
  rewrite -!muln2. by rewrite mulnA.

  (* c is something else *)

  (* SHL r2, c *)
  basicapply SHL_RI_rule => //.

  (* ADD r1, r2 *)
  basicapply ADD_RR_ruleNoFlags.

  try_basicapply IHnbits => //.
  rewrite expn1 -{2}(odd_double_half m) ODD. rewrite muln2. rewrite -addBA.
  rewrite mulnDl mul1n. rewrite mulB_addn. rewrite mulnC.
  by rewrite shlB_mul2exp mulB_muln.

  rewrite -(add1n nbits) in LT1.
  apply: leq_trans LT1.
  rewrite -{1}(add0n (1+nbits)). by rewrite leq_add2r.
  apply: leq_trans LT1.
  rewrite -addn1. by rewrite leq_add2l.
(* lsb is 0 *)

  basicapply IHnbits.
  rewrite expnS.
  rewrite -{2}(odd_double_half m) ODD add0n.
  rewrite mulnA. rewrite muln2.
  sbazooka.
  by rewrite -(addn1 c) -addnA add1n.
  done.
Qed.

Lemma add_mulcFastCorrect (r1 r2: NonSPReg) (d:DWORD):
  |-- Forall v, Forall w,
  basic
  (r1 ~= v ** r2 ~= w)
  (add_mulcFast r1 r2 d) empOP
  (r1 ~= addB v (mulB w d) ** r2?) @ OSZCP?.
Proof.
rewrite /add_mulcFast.
specintros => v w.

have LT: toNat d < 2^32 by apply toNatBounded.
autorewrite with push_at.
try_basicapply genCorrect => //. by rewrite expn0 muln1 toNatK.
Qed.

Definition screenWidth:DWORD := Eval compute in #160.
Eval showinstr in linearize (add_mulcFast EDI EDX screenWidth).
