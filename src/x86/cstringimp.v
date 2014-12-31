(*===========================================================================
    C-style string code
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.spectac x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor x86proved.x86.flags x86proved.x86.macros.
Require Import Coq.Strings.String x86proved.cstring Coq.Strings.Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* String s contains no null characters *)
Fixpoint zeroFree s :=
  if s is String c s' then charToBYTE c != #0 /\ zeroFree s' else True.

Lemma zeroFree_append (s1 s2: string) :
  zeroFree (s1 ++ s2) -> zeroFree s1 /\ zeroFree s2.
Proof. induction s1 => //. simpl; intuition. Qed.

(* A couple of trivial lemmas concerning strings *)
Lemma length_append (s1 s2: string) : length (s1 ++ s2) = length s1 + length s2.
Proof. induction s1 => //. by rewrite /= IHs1. Qed.

Lemma append_cons s1 c s2 : (s1 ++ String c s2 = (s1 ++ String c EmptyString) ++ s2)%string.
Proof. induction s1 => //. by rewrite /= IHs1.  Qed.

(* The bytes between p and q correspond precisely to the contents of string s *)
Fixpoint memIsString (p q: ADDR) (s: string)  :=
  if s is String c s
  then p :-> charToBYTE c ** memIsString (p +# 1) q s
  else p == q /\\ empSP.

(* The memory at [p] contains a null-terminated string [s]
   (Note that [s] should not itself not contain null characters) *)
Fixpoint pointsToCString (p: ADDR) (s: string) : SPred :=
  if s is String c s
  then p :-> charToBYTE c ** pointsToCString (p+#1) s
  else p :-> (#0:BYTE).

Lemma pointsToCStringCons p c s :
  pointsToCString p (String c s) -|- p :-> charToBYTE c ** pointsToCString (p+#1) s.
Proof. split; rewrite /pointsToCString; by ssimpl. Qed.

(* If [p] points to a C-string [prefix ++ suffix] then it can be split into memory
   from [p] to [p +# length prefix] containing [prefix] and [p +# length prefix]
   pointing to [suffix] *)
Lemma pointsToCString_append prefix : forall p suffix,
  pointsToCString p (prefix ++ suffix) |--
  memIsString p (p +# length prefix) prefix ** pointsToCString (p +# length prefix) suffix.
Proof. induction prefix => p suffix.
+ simpl (_ ++ _).  rewrite /memIsString. simpl (length _). rewrite addB0/=. sbazooka.
+ rewrite /memIsString-/memIsString pointsToCStringCons -/append.
rewrite -> IHprefix. simpl (length _). ssimpl. by rewrite -addB_addn add1n.
Qed.

Lemma pointsToCString_append_op prefix : forall p q suffix,
  memIsString p q prefix ** pointsToCString q suffix |--
  pointsToCString p (prefix ++ suffix).
Proof. induction prefix => p q suffix.
+ rewrite /=. sdestructs => /eqP ->. by ssimpl.
+ rewrite /=. ssimpl. by rewrite <- (IHprefix (p+#1) q).
Qed.


(* Given a pointer to a C-style string in RDI, return its length in RCX *)
Definition strlen : program :=
  (MOV RCX, (#0:QWORD);;
   while (CMP BYTE PTR [RDI + RCX + 0], BOPArgI _ #0) CC_Z false
     (INC RCX))%asm.

(* Correctness of strlen *)
Lemma strlen_correct p s :
  zeroFree s ->
  |-- basic RCX? strlen (RCX ~= #(length s))
    @ (OSZCP? ** RDI ~= p ** pointsToCString p s).
Proof.
  move => ISZF. rewrite /strlen.
  autorewrite with push_at.

  rewrite /(stateIsAny RCX). specintros => oldrcx.

  (* MOV RCX, 0 *)
  basic apply *. 

  (* WHILE *)
  (* Loop invariant is most easily expressed by splitting the string into
     a prefix and suffix. RCX contains the length of the prefix *)
  set (I := fun b =>
    Exists prefix, Exists suffix,
    s = (prefix ++ suffix)%string /\\ (if suffix is ""%string then true else false) == b /\\
    RDI ~= p ** RCX ~= #(length prefix) **
    pointsToCString p s ** OF? ** SF? ** CF? ** PF?).
  eapply basic_basic; first apply (while_rule_ro (I:=I)). 

  (* Condition code: CMP [RDX+RCX], 0 *)
  specintros => b1 b2.
  subst I; cbv beta.
  specintros => prefix suffix APPEND END.

  case E: suffix => [| a s']. 

  (* Empty string *)
  + rewrite /ConditionIs. rewrite E in END. 
  Hint Rewrite ->signExtend_fromNat : ssimpl. rewrite APPEND. 
  attempt basic apply *. subst. rewrite ->pointsToCString_append. rewrite /pointsToCString. ssimpl.
  by subst.
  rewrite <-pointsToCString_append_op. subst. unfold pointsToCString. by ssimpl. 

  (* Non-empty string *)
  + rewrite /ConditionIs. rewrite E in END.
  attempt basic apply *. subst.
  rewrite -> pointsToCString_append. rewrite /pointsToCString-/pointsToCString. by ssimpl.
  subst. destruct (zeroFree_append ISZF) as [_ [ZFM _]].
    rewrite subB0. by rewrite eq_sym eqbF_neg.
    subst. 
    rewrite <- pointsToCString_append_op. rewrite /pointsToCString-/pointsToCString/stateIsAny. by ssimpl. 

  (* Body of loop: INC ECX *)
  rewrite /ConditionIs/I.
  specintros => prefix suffix APPEND END. rewrite /stateIsAny. subst. specintros => ofl sfl cfl pfl.

  (* We would like to use basic apply but it's too eager to instantiate prefix and suffix *)
  rewrite /basic. specintros => i j. 
  Require Import basicspectac. 
  unfold_program. specapply *. rewrite /OSZCP. by ssimpl. 

  rewrite <- spec_frame. autorewrite with push_at. apply limplValid. cancel1. ssimpl.

  case E: suffix => [| a s'].

  (* Empty string *)
  + by subst.
  (* Non-empty string *)
  + subst. ssplit. ssplit. instantiate (1:= (prefix ++ String a EmptyString)%string).
    rewrite /OSZCP. sbazooka.
    by rewrite append_cons.
    rewrite length_append. simpl (length _). rewrite incB_fromNat addn1. by ssimpl.

  (**)
  subst I.
    rewrite /ConditionIs.
    rewrite /stateIsAny.
    sdestructs => o sf z c pf. sbazooka. instantiate (1:=s). by instantiate (1:=EmptyString).
    simpl (length _). rewrite /natAsDWORD. by ssimpl.
  subst I; cbv beta.
    sdestructs => prefix suffix -> END.
    rewrite /ConditionIs.
    destruct suffix => //.
    rewrite /stateIsAny. rewrite length_append addn0.
    sbazooka.
Qed.
