Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple tuplehelp.
Require Import path fingraph  finset.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr monad reader writer procstate procstatemonad mem exn eval instrcodec
               monadinst ioaction bitsrep bitsops eval step pointsto cursor.
Require Import program programassem programeq reg instrsyntax instrrules.
Require Import spectac iltac triple.
(*Require Import pecoff.*)

Require Import stringbuff.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Section Compiler.

(****************************************************************)
(* Arguments                                                    *)
(****************************************************************)

(* Interface: [acc]eptance and [rej]ection continuations *)
Variables 
  (acc: DWORD)
  (rej: DWORD).

(* Interface: address to a C-string buffer, and its content *)
Variables
  (buffer: DWORD)
  (str: seq DWORD).

(* Interface: automata *)
Variables
  (dfa_size: nat)
  (dfa_init: 'I_dfa_size)
  (alphabet: seq DWORD)
  (accept: 'I_dfa_size -> bool)
  (trans: 'I_dfa_size -> DWORD -> 'I_dfa_size).

Definition dfa_state := 'I_dfa_size.

(****************************************************************)
(* Helpers                                                      *)
(****************************************************************)

(* Language of a DFA: *)

(*=lang *)
Fixpoint lang (s: dfa_state) (w: seq DWORD): bool := 
  if w is a::w' 
  then (a \in alphabet) && lang (trans s a) w'
  else accept s.
(*=End *)


(* It is [safe] to [run] the code at address [k]: *)
Definition run (k: DWORD) := safe @ (EIP ~= k).
Hint Unfold run: specapply.



(* [runState] specifies the invariants necessary to run the transition
 * function of state [s]: *)
Definition runState
             (labels: dfa_size.-tuple DWORD)
             (s: dfa_state) :=
  run (tnth labels s)
        @ (Exists pd: DWORD,
           Exists l1: seq DWORD,
           Exists l2: seq DWORD,
           (CString l1)
        && (str == (cat l1 l2))
        && (lang s l2 == lang dfa_init str)
       /\\ (EAX ~= pd)
        ** EBX?
        ** (buffer -- pd :-> l1)
        ** (pd :-S> l2)).
Hint Unfold runState : specapply.

(* [runStates] specifies the invariants of all the states in
 * [DFA_state]: *)
Definition runStates 
             (labels: dfa_size.-tuple DWORD): spec :=
  Forall k: 'I_dfa_size, runState labels k.
Hint Unfold runStates : specapply.

(* [runAcc] states that to run the [acc] continuation, the string we
 * are parsing must be in the language of the DFA: *)
Definition runAcc :=
  run acc
      @ (lang dfa_init str
     /\\ EAX?
      ** EBX? 
      ** buffer :-S> str).
Hint Unfold runAcc: specapply.

(* Conversely, [runRej] states that to run the [rej] continuation, the
 * string must *not* be in the language: *)
Definition runRej :=
  run rej
      @ ((~~ (lang dfa_init str))
     /\\ EAX?
      ** EBX? 
      ** buffer :-S> str).
Hint Unfold runRej: specapply.

(****************************************************************)
(* Modules                                                      *)
(****************************************************************)

(*
 * Computation: jumpNext
 *
 * Compare a character [c] against [EBX] and jump to [next] if they
 * are equal. 
 *
 * Invariant: the point of this module is the specification
 * [jumpNext_logic] that reifies the invariant [c == v] for [EBX ~=
 * v].
 *
 *)
  
Section JumpNext.

Variables (c: DWORD)
          (next: DWORD).

Definition jumpNext : program :=
  CMP EBX, c ;;
  JE next.
Hint Unfold jumpNext: specapply.

Lemma jumpNext_logic 
        (i j: DWORD)(pd v : DWORD) :

 |-- (|> run next @ (v == c /\\ empSP)
  //\\   run j @ (v != c /\\ empSP)
 (* --------------------------------------- *)  -->> 
        run i)

 (* Memory: *)
      @ (EAX ~= pd ** EBX ~= v)
      @ OSZCP_Any

 (* Program: *)
     <@ (i -- j :-> jumpNext).
Proof.
  rewrite /jumpNext/run.
  unfold_program; specintros=> i1.

  (* RUN: CMP EBX, c *)
  specapply CMP_RI_eq_rule; first by sbazooka.

  (* RUN: JE next *)
  specapply JZ_rule; first by sbazooka.
  rewrite <-spec_reads_frame; autorewrite with push_at.
  apply limplValid; apply landR.
  
    * (* FLOW: run [next] *)
    apply landL1.
    do 2 cancel1.
    sdestruct=> /eqP ->.
    rewrite /OSZCP_Any/stateIsAny.
    by sbazooka.

    * (* FLOW: run [j] *)
    apply landL2.
    cancel1. 
    sdestruct=> /eqP ->.
    rewrite /OSZCP_Any/stateIsAny.
    by sbazooka.
Qed.

End JumpNext.

(*
 * Computation: jumpTable
 *
 * Compute the lookup table for a state [s], over the entire
 * [alphabet]. 
 *
 * Invariant: a jump is made to state [k] iff the character [v] in
 * [EBX] is in the alphabet and the DFA specifies a transition from
 * [s] to [k] upon a [v]. Otherwise, we exit the lookup table.
 *
 *)

Section JumpTable.

Variables (labels:  dfa_size.-tuple DWORD)
          (s : dfa_state).

Definition jumpTable :=
    foldr prog_seq prog_skip 
          [seq jumpNext c (tnth labels (trans s c))
          | c <- alphabet].


Lemma jumpTable_logic
        (i j: DWORD)(pd: DWORD)(v: DWORD) : 

 |-- ( (|>  Forall k: 'I_dfa_size, 
        run (tnth labels k) 
            @ ((v \in alphabet)
            && (trans s v == k)
            /\\ empSP ))
    //\\ (run j @ (v \notin alphabet /\\ empSP))
 (* ------------------------------------------------ *) -->> 
    run i)

 (* Memory: *)
      @ (EAX ~= pd ** EBX ~= v ** OSZCP_Any)

 (* Program: *)
     <@ (i -- j :-> jumpTable).
Proof.
  rewrite /jumpTable/run.
  elim: alphabet i j=> [i j /=|a l IH i j //].

  * (* CASE: alphabet ~ [::] *)
    specintros=> <-.
    rewrite <-spec_reads_frame.
    rewrite <-spec_frame.
    apply limplValid; apply landL2.
    autorewrite with push_at; cancel1.
    by sbazooka.

  * (* CASE: alphabet ~ a :: l *)
    rewrite [map _ (_ :: _)]/=.
    rewrite [foldr _ _ (_ :: _)]/=.
    unfold_program; specintros=> jumpTable.

    (* RUN: jumpNext a (tnth labels (next a)) *)
    specapply jumpNext_logic; first by ssimpl.
    specsplit.

    - (* CASE: v == a: run [tnth labels (next a)] *)
      rewrite <-spec_reads_frame; autorewrite with push_at.
      apply limplValid; apply landL1; cancel1.
      apply lforallL with (x := trans s a).
      autorewrite with push_at.
      do 2 cancel1.
      sdestruct=> /eqP ->.
      sbazooka.
      by apply/andP; split; 
         [ apply mem_head 
         | done].

    - (* CASE: v == a: run [jumpTable] *)      
      autorewrite with push_at.
      specintros=> neq_v_a.
      specapply IH; first by sbazooka; move=> {IH}.
      specsplit;
        rewrite <-spec_reads_frame;
        rewrite ->spec_at_emp;
        apply limplValid.
      + (* CASE: Forall k, |>safe @ (EIP~=tnth labels k) *)
        apply landL1; autorewrite with push_at; cancel1.
        apply lforallR=> k.
        apply lforallL with (x := k).
        cancel2; cancel1.
        sdestruct=> /andP [q1 q2].
        sbazooka; apply /andP; split; last by exact: q2.
        rewrite in_cons; apply/orP; apply or_intror.
        by exact: q1.
                
      + (* CASE: |>safe @ (EIP~=exit) //\\ safe @ (EIP~=j) *)
        apply landL2.
        autorewrite with push_at; cancel1.
        sdestruct=> q.
        sbazooka.
        rewrite in_cons; rewrite negb_or.
        apply/andP; split; exact.
Qed.

End JumpTable.


(*
 * Computation: nextChar
 *

 * Load the DWORD pointed by [EAX] into [EBX] and move the pointer to
 * the next DWORD in memory. If [EBX = #0], we have reached the end of
 * the string and jump to [exit].
 *

 * Invariant: We run [exit] iff we have reached the end of the string,
 * ie. [l2 ~ [::]]. Otherwise, we execute the next instructions with
 * the knowledge that [EBX] contains a non-null character [c] and the
 * string looks like [l1 ++ c :: l2].
 *
 *)

Section NextChar.

Variables (labels : dfa_size.-tuple DWORD)
          (s: dfa_state)
          (exit: DWORD).

Definition nextChar: program :=
    (* Move pointer to next character *)
    MOV EBX, [EAX] ;;
    ADD EAX, (#4 : DWORD) ;;
    (* Exit if end of string: *)
    jumpNext #0 exit.
Hint Unfold nextChar: specapply.

Lemma nextChar_logic
        (i j: DWORD)(hiBuff: DWORD)(pd: DWORD)(l1 l2: seq DWORD)(l1_string: CString l1) :

  |-- (run exit @ ((l2 == [::])
               /\\ EAX ~= hiBuff +# 4
                ** EBX?
                ** buffer -- hiBuff :-S> l1)
  //\\ run j @ (Exists c: DWORD,
                Exists l2': seq DWORD,
                (l2 == [:: c & l2' ])
             && (c != #0)
            /\\ EAX ~= pd +# 4
             ** EBX ~= c
             ** (buffer -- next (pd +# 3) :-> (cat l1 [:: c]))
             ** (next (pd +# 3) -- hiBuff :-S> l2'))
(* -------------------------------------*) -->>
   run i @ (EAX ~= pd
         ** EBX?
         ** buffer -- pd :-> l1 
         ** pd -- hiBuff :-S> l2))

  (* Memory: *)
     @ OSZCP_Any

  (* Program: *)
    <@ (i -- j :-> nextChar).
Proof.
  rewrite /nextChar/run. 
  unfold_program; specintros=> add jumpNext.
  
  case: l2=> [|c l2].

  * (* CASE: l2 = [::] *)
    rewrite ->caseString_nil.
    specintros=> eq_pd.

    (* RUN: MOV EBX, [EAX] *)
    specapply MOV_RanyM_rule;
      first by sbazooka;
               rewrite addB0;
               move/eqP: eq_pd ->;
               sbazooka.

    (* RUN: ADD EAX, 4 *)
    specapply ADD_RI_ruleNoFlags; 
      first by sbazooka.
   
    
    (* jumpNext #0 exit *)
    specapply jumpNext_logic; 
      first by rewrite /stateIsAny; 
               sbazooka.
 
    specsplit;
      rewrite <-spec_reads_frame; 
      autorewrite with push_at;
      apply limplValid.
   

    - (* CASE: end of string: run exit *)    
      apply landL1; rewrite <-spec_later_weaken; 
        cancel1; sdestruct=> _;
        rewrite addB0; rewrite /stateIsAny; 
        move/eqP: eq_pd=> ->;
        sbazooka.
      rewrite ->(emptyString l1_string).
      by reflexivity.

    - (* CASE: impossible: got a non zero at the end of string! *)
      apply landL2.
      cancel1.
      by sdestruct=> /eqP //.

  * (* CASE: l2 =~ [:: c & cs ] *) 
    rewrite ->caseString_cons.
    specintros=> c_neq_0.

    (* MOV EBX, [EAX] *)
    specapply MOV_RanyM_rule;
      first by sbazooka;
               rewrite addB0;
               sbazooka.

    (* ADD EAX, 4 *)
    specapply ADD_RI_ruleNoFlags; first by sbazooka.

    (* jumpNext #0 exit *)
    specapply jumpNext_logic; first by sbazooka.

    specsplit;
      rewrite <-spec_reads_frame; autorewrite with push_at;
      apply limplValid.

    - (* CASE: impossible: end of string *)
      apply landL1;
        rewrite <-spec_later_weaken; 
        do 2 cancel1.
      sdestruct=> /eqP c_eq_0.
      by rewrite c_eq_0 // in c_neq_0.

    - (* CASE: run [j] *)
      apply landL2; cancel1; 
      rewrite /stateIsAny  [pd +# 0] addB0;
        ssimpl;
        sdestruct=> _.
      sbazooka;
        first by apply/andP; split; done || assumption. 
      rewrite seqMemIsCat pairMemIsPair /pointsTo.
      sdestruct=> q'; sbazooka. 
      rewrite ->memIsFixed. sdestruct => H. apply apart_addBn_next in H. rewrite H. 
      rewrite ->seqMemIsCons; sbazooka.
      by rewrite seqMemIsNil; sbazooka.
Qed.

End NextChar.

(*
 * Computation: transitionState
 * 
 * The code generated by [transitionState] corresponds to the
 * transition function for a given state [s]. It is basically a jump
 * table, mapping over the alphabet and jumping to whichever state
 * matches. If none matches, it jumps to accept or reject, depending
 * on whether the state itself is accepting or not.
 * 
 * Invariant: a jump to [acc] (resp. [rej]) is made iff the word in
 * memory is accepted (resp. rejected). Otherwise, we maintain the
 * invariant that the currently processed input is accepted iff the
 * word is accepted.
 * 
 *)

Section TransitionState.

Variables (labels : dfa_size.-tuple DWORD)
          (s: dfa_state).

Definition transitionState : program :=
  (tnth labels s):;;
    (* Increment but stay inside buffer *)
    nextChar (match accept s with
                | true => acc 
                | false => rej
              end);;
    (* Jump table: *)
    jumpTable labels s ;;
    (* Char not in alphabet: *)
    JMP rej.

Lemma transitionState_logic 
        (i j: DWORD) :

  |--    (|> runStates labels
      //\\ runAcc
      //\\ runRej
   (* -------------------------------------------- *) -->>
      runState labels s)

   (* Memory: *)
     @ OSZCP_Any

   (* Program: *)
     <@ (i -- j :-> transitionState).
Proof.
  rewrite /transitionState.
  unfold_program; specintros=> _ <- -> jmpTable jumpErr.
  rewrite /runState/run/pointsToS.
  specintros=> pd l1 l2 /andP [/andP [l1_string eq_str_l1_l2] lang_invariant] hiBuff.

  (* Get nextChar *)
  specapply nextChar_logic;
    [ by sbazooka 
    | 
    | by assumption].
  specsplit.

  - (* CASE: end of string *)

    (* RUN: [if accept s then acc else rej] *)
    specintros=> /eqP eq_l2_nil.
    rewrite eq_l2_nil {1}/lang in lang_invariant.
    case: (accept s) lang_invariant => lang_invariant;
      rewrite <-spec_reads_frame;
      autorewrite with push_at;
      apply limplValid; apply landL2.

      + (* CASE: accepting state *)
        apply landL1.
        rewrite /runAcc/run/stateIsAny/pointsToS;
          autorewrite with push_at; 
          cancel1;
          sbazooka.
        rewrite eq_l2_nil cats0 in eq_str_l1_l2.
        move/eqP: eq_str_l1_l2=> ->.
        by reflexivity.

      + (* CASE: rejecting state *)
        apply landL2.
        rewrite /runRej/run/stateIsAny/pointsToS;
          autorewrite with push_at; 
          cancel1; sbazooka.
        rewrite eq_l2_nil in eq_str_l1_l2.
        move/eqP: eq_str_l1_l2=> ->.
        rewrite cats0.
        by reflexivity.

  - (* CASE: non empty string *)

    (* RUN: jumpTable labels s *)
    specintros=> c l2' /andP [eq_l2_c_l2' neq_c_0].
    move/eqP: eq_l2_c_l2'=> -> in eq_str_l1_l2 lang_invariant.
    specapply jumpTable_logic; first by sbazooka.
    specsplit.

    * (* CASE: c matched a rule *)

      (* RUN: state k *)
      rewrite <-spec_reads_frame; autorewrite with push_at.
      apply limplValid; apply landL1.
      rewrite ->spec_later_forall.
      rewrite /runStates.
      specintros=> k; cancel1; 
        autorewrite with push_at;
        apply lforallL with (x := k).
      rewrite /runState/run/stateIsAny.
      autorewrite with push_at;
        do 2 cancel1.
      sdestruct=> /andP [c_in_alphabet trans_s_c].
      sbazooka.
      do 2 try (apply/andP; split); first 1 last.
      * (* str == (l1 ++ [:: c]) ++ l2' *)
        have: str == ((l1 ++ [:: c]) ++ l2')%SEQ
          by move/eqP: eq_str_l1_l2 ->;
             rewrite -cat_rcons -cats1.
        by move/eqP=> ->.

      * (* lang k l2' == lang DFA_init str *)
        move/eqP: lang_invariant <-.
        move/eqP: trans_s_c <-.
        rewrite [lang _ (_ :: _)]/=.
        rewrite c_in_alphabet.
        by rewrite /=.


      * (* CString (l1 ++ [:: c]) *)
        rewrite /CString.
        rewrite all_cat.
        by apply/andP; split;
          try rewrite all_seq1;
          assumption.

      * (* Same memory *)
        rewrite /pointsToS/memToS.
        rewrite -> (@memIsNonTop _ _ l2' (next (pd +# 3)) hiBuff). 
        sdestructs=> l2'_is_string pd' eq_pd_4_pd'.
        rewrite eq_pd_4_pd'.
        apply nextIsInc in eq_pd_4_pd'.
        rewrite -addB_addn in eq_pd_4_pd'.
        rewrite  eq_pd_4_pd'.
        by sbazooka.

      (* RUN: JMP rej *)
      specintros=> c_notin_alphabet.
      specapply JMP_I_rule; first by sbazooka.

      (* RUN: [rej] *)
      rewrite /runRej/run.
      rewrite <-spec_reads_frame; autorewrite with push_at.
      apply limplValid; do 2 apply landL2.
      rewrite <-spec_later_weaken; cancel1; rewrite /stateIsAny.

      have eq_l1_c_l2': str == ((l1 ++ [:: c]) ++ l2')%SEQ
          by move/eqP: eq_str_l1_l2 ->;
             rewrite -cat_rcons -cats1.

      sbazooka.
      - (* CASE: ~~ lang dfa_init str *)
        move/eqP: lang_invariant=> <-.
        rewrite [lang _ (_ :: _)]/=.
        rewrite negb_and.
        apply/orP; apply or_introl.
        by exact: c_notin_alphabet.

      - (* CASE: splitting of str *)
        rewrite /pointsToS/memToS. 
        rewrite ->(@memIsNonTop _ _ l2' (next (pd +# 3)) hiBuff). 
        sdestructs=> l2'_is_string pd' eq_pd_4_pd'. 
        rewrite eq_pd_4_pd'.
        apply nextIsInc in eq_pd_4_pd'.
        rewrite -addB_addn in eq_pd_4_pd'.
        rewrite -eq_pd_4_pd'.
        sbazooka;
          move/eqP: eq_l1_c_l2' => ->.
        
        * (* CASE: CString str *)          
          rewrite /CString;
            do 2 rewrite all_cat; 
            rewrite all_seq1.
          by do 2 try (apply/andP; split);
            assumption.

        * (* CASE: str splitting in memory *)
          rewrite ->(seqMemIsCat _ _ (l1 ++ [:: c])%SEQ).
          rewrite ->pairMemIsPair.
          by sbazooka.
Qed.

(*
  Unfolding the various modules used to [transitionState], we obtain
  the following [transition] program:
*)

(*=transition *)
Definition transition : program :=
  (tnth labels s):;;

    (* Move pointer to next character *)
    MOV EBX, [EAX] ;;
    ADD EAX, (#4 : DWORD) ;;

    (* Accept/reject if end of string: *)
    CMP EBX, (#0: DWORD) ;;
    JE (if accept s then acc else rej);;

    (* Jump table: *)
    foldr prog_seq prog_skip 
          [seq CMP EBX, (c: DWORD) ;;
               JE (tnth labels (trans s c))
          | c <- alphabet] ;;

    (* Not in alphabet: *)
    JMP rej.
(*=End *)


(* 

  We can therefore prove that the code given in the paper is
  (syntactically) equivalent to the one on which we did the proof:

*)

Lemma equiv_transition: progEq transition transitionState.
Proof.
  apply program_equal.
  rewrite /transition.
  rewrite /transitionState/nextChar/jumpTable/jumpNext/norm//=.
  case (accept s);
    do ! (apply progEqSeq; try apply progEqRefl).
Qed.
  
End TransitionState.


(*
 * Computation: compileDFA
 * 
 * Having compiled the transition function of a single state, we need
 * to iterate it over all states. We simply concatenate each
 * transition functions in (program) memory: during assembly, the
 * labels will resolve to the correct address. 
 * 
 * Invariant: the invariant is exactly the same as it was for a single
 * transition ([transitionState_logic]), excepted that, this time, the
 * memory does not contain one transition function but all the others
 * too.
 * 
 *)

(* 
 * For convenience, we use the following helper function and lemma,
 * which are defined over an index [n]. This lets us proceed by
 * ordinal induction over an 'I_n instead of working directly over
 * 'I_dfa_size. This way, we don't need to clear the things in context
 * that depends on dfa_size too.
 *)

Definition dfaProg n : ('I_n -> program) -> program :=
  @nathelp.nat_ind (fun n => ('I_n -> program) -> program)
           (fun _ => prog_skip)
           (fun n IHn compileState => compileState ord0 ;;
                                      IHn (fun k => compileState (ordS k)))
           n.

Lemma dfaProg_logic n
        (P: 'I_n -> spec) 
        (code: 'I_n -> program):

    (forall s: 'I_n,
     forall i j: DWORD, |-- P s <@ (i -- j :-> code s))
 (* ------------------------------------------------------ *)-> 
    forall s: 'I_n,
      forall i j: DWORD, |-- P s <@ (i -- j :-> dfaProg code).

Proof.
  move=> H s.
  rewrite /dfaProg.
  induction s using ord_ind;
    move=> i j;
    rewrite [nathelp.nat_ind _ _ (n.+1)]/=;
    unfold_program; specintros=> i'.
  * (* CASE: s ~ ord0 *)
    rewrite <-spec_reads_merge.
    rewrite <-spec_reads_frame.
    by exact: H.

  * (* CASE: s ~ ordS s *)
    rewrite ->sepSPC1.
    rewrite <-spec_reads_merge.
    rewrite <-spec_reads_frame.
    apply (IHs (fun k => P (ordS k))) => s'.
    by exact: H.
Qed.


Section CompileDFA.

Variable (labels: dfa_size.-tuple DWORD).

Definition compileDFA :=
  dfaProg (transitionState labels).

Lemma compileDFA_logic
          (s: 'I_dfa_size)
          (i j: DWORD):

    |-- ((|> runStates labels)
       //\\ runAcc
       //\\ runRej
 (* ------------------------------------------------*) -->> 
       runState labels s)
       
 (* Memory: *)
     @ OSZCP_Any

 (* Program: *)
    <@ (i -- j :-> compileDFA).
Proof.
  move: s i j.
  apply dfaProg_logic=> s i j.
  rewrite /runState/run.
  specintros=> k l1 l2 H_l1_l2.
  specapply transitionState_logic;
    first by sbazooka.
  by rewrite /runStates/runState/run;
     rewrite <-spec_reads_frame;
     rewrite ->spec_at_emp;
     apply limplAdj;
     apply landL2;
     reflexivity.
Qed.

End  CompileDFA.

(*
 * Logic: concatRuns
 * 
 * In [compileDFA_logic], we have shown that we can execute the
 * transition function for a given state [s] provided that the code of
 * all transitions is in memory. Now, we prove that we can execute
 * *any* transition function in such a configuration.
 * 
 * Invariant: we therefore generalize the post-condition to [runStates
 * labels].
 * 
 *)

Section ConcatRuns.

Variable (labels: dfa_size.-tuple DWORD).

Lemma concatRuns_logic (i j: DWORD) :

    |-- ((|> runStates labels)
       //\\ runAcc
       //\\ runRej
 (* ------------------------------------------------*)
       -->> runStates labels)
       
 (* Memory: *)
     @ OSZCP_Any

 (* Program: *)
    <@ (i -- j :-> compileDFA labels).

Proof.
  etransitivity;
    first by apply lforallR;
             move=> s;
             apply (@compileDFA_logic labels s i j).
  rewrite /runStates; specintros=> k.
  apply lforallL with k.
  by reflexivity.
Qed.

End ConcatRuns.

(*
 * Logic: lobRuns
 * 
 * In [concatRuns], we prove that if *later* we can jump to any
 * transition function, then we can take any transition function
 * now. By generalizing the Löb rule, we can absorb the premise and
 * jump straight to the conclusion.
 *
 * Invariant: if we can take the [acc]epting or the [rej]ecting
 * continuations, then we can run any transition function.
 * 
 *)


Section LobRuns.

Variables (labels: dfa_size.-tuple DWORD).


Lemma lobRuns_logic (i j: DWORD) :

    |-- (runAcc
    //\\ runRej 
 (* ------------------------------------------------*) -->>
         runStates labels)
       
 (* Memory: *)
     @  OSZCP_Any
 (* Program: *)
    <@ (i -- j :-> compileDFA labels).

Proof.
  etransitivity; 
    first by apply concatRuns_logic.
  cancel2; last (by reflexivity); cancel2.
  rewrite [(|> _) //\\ _]landC.
  apply limplAdj.
  apply spec_lob_context.
  do 2 rewrite landA.
  apply limplL; 
    [ | apply landL1];
    by reflexivity.
Qed.

End LobRuns.


(*
 * Computation: startDFA
 *
 * To run our automaton, we are just left with jumping to the initial
 * state.
 *
 * Invariant: we have specialized the invariant from [lobRuns_logic]
 * above and unfolded its definitions a little bit, for clarity. We
 * therefore have that if we can take the [acc]epting
 * (resp. [rej]ecting) continuation (provided that the word is
 * accepted (resp. rejected)), then we can run the automaton (provided
 * that [EAX] points to the beginning of a string buffer).
 *
 *)

Section StartDFA.

Variable
  (labels: dfa_size.-tuple DWORD).

Definition start: program :=
  JMP (tnth labels dfa_init);;
  compileDFA labels.

Lemma start_logic 
        (i j: DWORD):

    |-- (((run acc @ (lang dfa_init str
                  /\\ EAX?))
    //\\ (run rej @ (~~ (lang dfa_init str)
                  /\\ EAX?)))
 (* ------------------------------------------------*) -->> 
         run i @ (EAX ~= buffer))
       
 (* Memory: *)
     @ OSZCP_Any
     @ EBX?
     @ (buffer :-S> str)

 (* Program: *)
    <@ (i -- j :-> start).

Proof.
  rewrite /start/run.
  unfold_program; specintros=> codeDFA.

  (* Run: JMP (tnth labels dfa_init *)
  specapply JMP_I_rule; first by sbazooka.
  rewrite <-spec_later_weaken.

  (* Apply: correctness of compileDFA *)  
  rewrite [(_ -- _ :-> _) **( _ -- _:-> _)]sepSPC.
  rewrite <-spec_reads_merge.
  rewrite <-spec_reads_frame.
  etransitivity; first by apply lobRuns_logic.
  (* Delete read frame *)
  cancel2; last by reflexivity.
  (* Delete frame *)
  autorewrite with push_at.

  apply limplAdj; apply limplL.
    * (* CASE: post-conditions --> runAcc /\ runRej *)
      rewrite /runAcc/runRej/stateIsAny/run/pointsToS.
      specsplit.

      - (* CASE: Accepting is implied *)
        apply landL1.
        autorewrite with push_at; cancel1.
        sdestruct=> q; ssplit; first by exact.
        by sbazooka.

      - (* CASE: Rejecting is implied *)      
        apply landL2.
        autorewrite with push_at; cancel1.
        by sbazooka.

    * (* CASE: pre-conditions --> can run dfa_init label *)
      rewrite /runStates/runState/run/stateIsAny/pointsToS.
      autorewrite with push_at.
      apply landL1.
      apply lforallL with (x := dfa_init).
      autorewrite with push_at; cancel1.
      sdestruct=> v.
      ssimpl.
      apply lexistsR with (x := buffer).
      apply lexistsR with (x := [::]).
      apply lexistsR with (x := str).
      sbazooka.
      do 2 try (apply/andP; split); done.
      rewrite seqMemIsNil.
      sbazooka.
Qed.


(*
 *
 * In the paper, we wrote the following definition for the compiler,
 * which is a mere unfolding of the above [start] definition.
 *
 *)

(*=DFA_to_x86 *)
Definition DFA_to_x86: program :=
  JMP (tnth labels dfa_init);;
  foldr prog_seq prog_skip
        [tuple transition labels s
        | s < dfa_size].
(*=End *)

(* 
 * The two programs are (syntactically) equivalent, by
 * [equiv_DFA_to_x86] below:
 *)

Lemma equiv_dfaProg_fold n (f: 'I_n -> program) : 
  progEq (dfaProg f)
         (foldr prog_seq prog_skip [tuple (f s) | s < n]). 
Proof.
  rewrite /dfaProg.
  elim: n f=> [f|n IH f].
  * (* CASE: n ~ 0 *)
    have-> : [tuple f s  | s < 0] = [tuple] 
      by apply tuple0. 
    by apply progEqRefl.
  * (* CASE: n ~ suc n *)
    rewrite enum_eta. 
    apply progEqSeq; try apply progEqRefl.
    apply IH.
Qed.

Lemma fold_equiv n (f g : 'I_n -> program)
                 (H: forall k:'I_n, progEq (f k) (g k)): 
  progEq (foldr prog_seq prog_skip [tuple f s | s < n])
         (foldr prog_seq prog_skip [tuple g s | s < n]).
Proof.
  elim: n f g H=> [f g k|n IH f g H].
  * (* CASE: n ~ 0 *)
    by do 2 rewrite [[tuple _ s  | s < 0]] tuple0;
       apply progEqRefl.

  * (* CASE: n ~ n+1 *)
    do 2 rewrite enum_eta.
    do 2 rewrite /(foldr _ _ (_ :: _)).
    apply progEqSeq; first by exact: H.
    apply (IH (fun k => f (ordS k)) (fun k => g (ordS k))).
    move=> k.
    apply H.
Qed.

Lemma equiv_DFA_to_x86: progEq DFA_to_x86 start.
Proof.
  rewrite /DFA_to_x86/start.
  apply progEqSeq; try apply progEqRefl.
  rewrite /compileDFA.
  apply progEqTrans with (p2 := (foldr prog_seq prog_skip [tuple transitionState labels s  | s < dfa_size])).
  * apply fold_equiv.
    move=> k.
    apply equiv_transition.
  * by apply progEqSym;
       apply equiv_dfaProg_fold.
Qed.

(*
 *
 * By substitutivity of program equivalences, we thus obtain the
 * correctness of our compiler:
 *
 *)

Lemma DFA_to_x86_correct :

    |-- Forall l: DWORD, Forall m: DWORD,

    (   (safe @ (lang dfa_init str 
                /\\ EIP ~= acc) @ EAX?)
   //\\ (safe @ (~~ lang dfa_init str
                /\\ EIP ~= rej) @ EAX?)
   (* ----------------------------------*) 
    -->>  safe @ (EIP ~= l) @ (EAX ~= buffer) )

   (* Memory: *)
     @ OSZCP_Any
     @ EBX?
     @ (buffer :-S> str)

   (* Program: *)
     <@ (l -- m :-> DFA_to_x86).

Proof.
  specintros=> l m.
  rewrite ->equiv_DFA_to_x86.
  etransitivity; 
    first by apply start_logic.
  rewrite /run.
  cancel2; last (by reflexivity); cancel2.
  autorewrite with push_at.
  apply limplAdj; apply limplL;
    last by apply landL1.
  specsplit;
    [ apply landL1
    | apply landL2];
    cancel1; sbazooka.
Qed.

End StartDFA.

(* 
 * We generate the program labels by iterated application
 * [prog_declabel]:
 *)

Fixpoint mkLabelsHelp
           (n : nat) : (n.-tuple DWORD -> program) -> program :=
  match n with
    | 0 => fun g => g [tuple]
    | n.+1 => fun g => prog_declabel (fun a => 
                       mkLabelsHelp (fun ls =>
                       g [tuple of a :: ls]))
  end.

Definition mkLabels
             (body: dfa_size.-tuple DWORD -> program) 
           : program :=
  mkLabelsHelp (fun ls => body ls).

Definition compiler : program :=
  mkLabels (fun labels => start labels).

End Compiler.