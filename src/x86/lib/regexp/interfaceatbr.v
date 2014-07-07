Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.finfun Ssreflect.fintype Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsprops.
Require Import x86proved.x86.program.

Require Import stringbuff.
Require Import compiler.

(* ATBR *)
(*Require Import ATBR.Common.*)
Require Import ATBR.Classes.
Require Import ATBR.Graph.
Require Import ATBR.DecideKleeneAlgebra.
Require Import ATBR.DKA_Definitions.
Close Scope A_scope.

(* BinPos *)
Require Import BinNums BinPos.



(****************************************************************)
(* Interface with RelationAlgebra                               *)
(****************************************************************)

Section Compile.

Variables
  (r: regex)
  (alphabet: seq DWORD).

Definition dfa_r: DFA.t := X_to_DFA r.

Lemma dfa_br: DFA.bounded dfa_r.
Proof.
  apply X_to_DFA_bounded.
Qed.

(*Coercion Pos.to_nat : positive >-> nat.*)
(*Coercion Pos.of_nat : nat >-> positive.*)

Notation char := positive.

Definition char_of_DWORD (n: DWORD) : char := Pos.of_nat (toNat n).
Definition DWORD_of_char (p: char): DWORD := #((Pos.to_nat p)).

(*
Lemma char_of_DWORDK (c: DWORD):
  c \in alphabet -> DWORD_of_char (char_of_DWORD c) = c.
Proof.
  move=> H; apply alphabet_char in H.
  rewrite /char_of_DWORD/DWORD_of_char.
  rewrite (Pnat.Nat2Pos.id);
    first by apply  toNatK.
  set x := toNat c.
  rewrite -(toNat_fromNat0 32).
  rewrite /x {x}.
  rewrite /not=> H'.
  apply  toNat_inj in H'.
  apply H.
  assumption.
Qed.
*)

(*
Coercion char_of_DWORD : DWORD >-> char.
Coercion DWORD_of_char : char >-> DWORD.
*)

Definition dfa_size: nat := (Pos.to_nat (DFA.size dfa_r)).-1.

Notation state := positive.


Lemma ord_of_belongHelp (s: state): DFA.belong s dfa_r -> (Pos.to_nat s).-1 < dfa_size.
Proof.
  move=> H.
  apply/ltP.
  rewrite /dfa_size.
  apply Lt.lt_pred.
  rewrite prednK;
    last by apply/ltP;
            apply Pnat.Pos2Nat.is_pos.
  rewrite -Pnat.Pos2Nat.inj_lt.
  exact: H.
Qed.

Definition ord_of_belong (s: state)(H: DFA.belong s dfa_r): 'I_dfa_size :=
  Ordinal (ord_of_belongHelp s H).

Lemma ord_of_belongK: forall s q, state_of_nat (nat_of_ord (ord_of_belong s q)) = s.
Proof.
  move=> s q.
  rewrite /ord_of_belong/=/state_of_nat.
  rewrite Pos.of_nat_succ prednK;
    last by apply/ltP;
            apply Pnat.Pos2Nat.is_pos.
  by rewrite Pnat.Pos2Nat.id.
Qed.

Definition DFA_init: 'I_dfa_size := ord_of_belong (DFA.initial dfa_r) (DFA.bounded_initial dfa_br).

Definition accept (s: 'I_dfa_size): bool := StateSet.mem s (DFA.finaux dfa_r).

Definition trans (s: 'I_dfa_size)(v: DWORD): 'I_dfa_size :=
  ord_of_belong (DFA.delta dfa_r (Pos.of_nat (toNat v) (* this is safe because v <> #0 *)) s)
                (DFA.bounded_delta dfa_br _ _).

Definition lang' (s: 'I_dfa_size)(w: seq DWORD): bool :=
  lang alphabet accept trans s w.



Lemma in_mem t s : StateSet.mem t s <-> StateSet.In t s.
Proof.
  split; [apply StateSet.mem_1 | apply StateSet.mem_2].
Qed.

Lemma equiv_read_lang
      (w: seq DWORD)
      (s: state)(q: DFA.belong s dfa_r) :
   StateSet.mem
     (DKA_DFA_Language.read dfa_r [seq char_of_DWORD c | c <- w] s)
     (DFA.finaux dfa_r) /\ (all (fun a => a \in alphabet) w)
   <-> lang' (ord_of_belong s q) w.
Proof.
  elim: w s q=> [s q|a w IH s q].
  * (* CASE: w ~ [::] *)
    rewrite /map/lang'/lang/accept/DKA_DFA_Language.read /=.
    rewrite /statesetelt_of_nat/state_of_nat.
    rewrite Pos.of_nat_succ.
    rewrite prednK;
         last by apply/ltP;
                 apply Pnat.Pos2Nat.is_pos.
    rewrite Pnat.Pos2Nat.id.
    by split; [ move=> [a _]; assumption
              | move=> a; split; assumption || done].

  * (* CASE: w ~ i :: a *)
    rewrite [map _ (_ :: _)]/=.
    rewrite /lang' [lang _ _ _ _ (_ :: _)]/=.
    rewrite [DKA_DFA_Language.read _ (_ :: _) _]/=.
    rewrite [all _ (_ :: _)]/=.

    rewrite [(trans (ord_of_belong s q) a)]/trans.
    rewrite ord_of_belongK.
    rewrite /char_of_DWORD.

    split.

    - (* CASE: read -> lang *)
      move=> [HMem /andP [a_in_alphabet all_in_w]].
      apply/andP; split; first by assumption.

      move: IH=> /(_ (DFA.delta dfa_r (char_of_DWORD a) s)
                  (DFA.bounded_delta dfa_br (char_of_DWORD a) s)) IH.

      by apply IH; split; by assumption.

    - (* CASE: lang -> read *)
      move=> /andP [a_in_alpha in_lang].

      apply IH in in_lang.
      move: in_lang=> [in_mem all_in_w].

      by split; try (apply/andP; split); assumption.
Qed.

Lemma lang_in_alphabet (s: 'I_dfa_size)(w: seq DWORD):
  lang' s w -> all (fun a => a \in alphabet) w.
Proof.
  elim: w s=> [_ _|a w IH s H] //=.
  rewrite [lang' _ (_ :: _)]/= in H.
  move/andP: H=> [a_in_alphabet lang_w].
  apply/andP; split; first by assumption.
  move: IH=> /(_ (trans s a) lang_w).
  done.
Qed.

Variable
  (alphabet_compat:
     forall c, c \in alphabet ->
                     below (char_of_DWORD c) (DFA.max_label dfa_r)).

Lemma lang_is_bounded (w: seq DWORD):
  lang' DFA_init w -> DKA_DFA_Language.bounded_word dfa_r [seq char_of_DWORD c | c <- w].
Proof.
  rewrite /DKA_DFA_Language.bounded_word.
  move=> w_in_lang c c_in_w.
  have w_in_alphabet: all (fun a => a \in alphabet) w
    by apply lang_in_alphabet with DFA_init;
       assumption.
  clear w_in_lang.
  elim: w w_in_alphabet c_in_w=> [_ _|a w IH w_in_alphabet c_in_w]//=.

  rewrite [map _ (_ :: _)]/= in c_in_w.
  rewrite [List.In _ (_ :: _)]/= in c_in_w.

  rewrite [all _ (_ :: _)]/= in w_in_alphabet.
  move: w_in_alphabet=> /andP [a_in_alphabet w_in_alphabet].
  move: c_in_w=> [<- | c_in_w].

  * (* CASE: below (char_of_DWORD a) (DFA.max_label dfa_r)
             with a \in alphabet *)
    apply: alphabet_compat.
    by done.

  * (* CASE: below c (DFA.max_label dfa_r)
             with c \in w *)
    move: IH=> /(_ w_in_alphabet c_in_w).
    by done.
Qed.

Lemma equiv_DFA_language
      (w: seq DWORD) :
  DKA_DFA_Language.DFA_language dfa_r [seq char_of_DWORD c | c <- w] /\ (all (fun a => a \in alphabet) w)
  <-> lang' DFA_init w.
Proof.
  rewrite /DKA_DFA_Language.DFA_language.
  split.
    * (* CASE: read -> lang *)
      move=> [[read _] bounded].
      rewrite /DFA_init.
      rewrite -(equiv_read_lang w (DFA.initial dfa_r) ((DFA.bounded_initial dfa_br))).
      rewrite in_mem.
      by split; assumption.

    * (* CASE: lang -> read *)
      move=> inLang.
      rewrite -in_mem and_assoc
              [_ /\ all _ _]and_comm -and_assoc.
      split;
        first by rewrite (equiv_read_lang w (DFA.initial dfa_r) ((DFA.bounded_initial dfa_br)));
                 assumption.
      by apply lang_is_bounded; assumption.
Qed.


Lemma test: (DKA_DFA_Language.DFA_language (X_to_DFA r) ==
            DKA_DFA_Language.regex_language r)%A.
apply equal_trans with (DKA_DFA_Language.regex_language (DFA.eval (X_to_DFA r))); last first.
apply DKA_DFA_Language.regex_language_graph_functor.
apply X_to_DFA_correct.
rewrite DKA_DFA_Language.language_DFA_eval.
reflexivity.
exact: dfa_br.
Qed.

Lemma compiler_correct (w: seq DWORD):
      lang' DFA_init w <->
         DKA_DFA_Language.regex_language r (map char_of_DWORD w)
      /\ (all (fun a => a \in alphabet) w).
Proof.
  rewrite -(test (map char_of_DWORD w)).
  rewrite /dfa_r.
  rewrite -equiv_DFA_language.
  done.
Qed.


Definition X_to_x86 (acc rej: DWORD): program :=
  compiler acc rej DFA_init alphabet accept trans.

End Compile.

(*
Definition X_to_x86
             (r: regex)
             (acc rej: DWORD): program :=
  DFA_to_x86 (X_to_DFA r) acc rej.
*)
