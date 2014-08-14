Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.seq.
Require Import x86proved.spred.
Require Import x86proved.common_tactics x86proved.charge_lemmas.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Existentials.
  Inductive term :=
  | t_atom (P: SPred)
  | t_star (t1 t2: term)
  | t_ex A (f: A -> SPred)
  | t_propand (P: Prop) (Q: SPred).

  Fixpoint eval (t: term) : SPred :=
    match t with
    | t_atom P => P
    | t_star t1 t2 => eval t1 ** eval t2
    | t_ex _ f => lexists f
    | t_propand P Q => P /\\ Q
    end.

  Record find_res := mkf {
    find_type: Type;
    find_closure: find_type -> SPred
  }.

  (**
     Given a term t, when this function succeeds, it will return an SPred with
     one existential quantifier removed and the quantified variable free.
     Notice:
     - Recall that [P /\\ Q] is defined at [Exists _: P, Q], so that works too.
     - We do eval as part of this process rather than afterwards. This is
       because as soon as we represent "terms with a free variable" as
       functions, there isn't any structure left to do elimination on anyway.
     - There is no attempt to find multiple existentials. This keeps the code
       simple, and the tactic needs to be iterated in any case as long as we
       don't look under binders to find nested existentials.
     - The [term] type is a bit wasteful since it reflects the whole formula
       despite only needing the path down to the first existential. Optimising
       that may require more Ltac programming, so it is not guaranteed to be
       faster.
  *)
  Fixpoint find (t: term) : option find_res :=
    match t with
    | t_atom _ => None
    | t_star t1 t2 =>
        match find t1 with
        | Some (mkf _ f1) => Some (mkf (fun P' => (f1 P') ** eval t2))
        | None =>
            match find t2 with
            | Some (mkf _ f2) => Some (mkf (fun P' => eval t1 ** (f2 P')))
            | None => None
            end
        end
    | t_ex _ f => Some (mkf f)
    | t_propand P Q => Some (mkf (fun _: P => Q))
    end.

  Lemma find_correct_pull t:
    match find t with
    | Some (mkf _ f) => eval t |-- Exists a, f a
    | None => True
    end.
  Proof.
    elim: t; red => //.

      rewrite -/find /eval -/eval.
      move=> t1 Ht1 t2 Ht2.
      destruct (find t1) as [[A f]|].
      - rewrite ->Ht1. apply: sepSPAdj. apply: lexistsL => a. apply: wandSPAdj.
        by apply lexistsR with a.
      destruct (find t2) as [[A f]|].
      - rewrite ->Ht2. rewrite sepSPC. apply: sepSPAdj. apply: lexistsL => a.
        apply: wandSPAdj. rewrite sepSPC. by apply lexistsR with a.
      done.

      reflexivity.

      reflexivity.
  Qed.

  Lemma find_correct_push t:
    match find t with
    | Some (mkf _ f) => Exists a, f a |-- eval t
    | None => True
    end.
  Proof.
    elim: t; red => //.
    - rewrite -/find /eval -/eval.
      move=> t1 Ht1 t2 Ht2.
      destruct (find t1) as [[A f]|].
      - apply: lexistsL => a. cancel2. rewrite <-Ht1. by apply lexistsR with a.
      destruct (find t2) as [[A f]|].
      - apply: lexistsL => a. cancel2. rewrite <-Ht2. by apply lexistsR with a.
      done.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma find_correct t:
    match find t with
    | Some (mkf _ f) => eval t -|- Exists a, f a
    | None => True
    end.
  Proof.
    move: (@find_correct_push t) (@find_correct_pull t).
    case: (find t); last done. move=> []; by split.
  Qed.

  Lemma find_lhs t Q:
    match find t with
    | Some (mkf _ f) => (forall a, f a |-- Q) -> eval t |-- Q
    | None => True
    end.
  Proof.
    move: (@find_correct_pull t). destruct (find t) as [[A f]|]; last done.
    move=> Heval HQ. rewrite ->Heval. exact: lexistsL.
  Qed.

  Lemma find_rhs t P:
    match find t with
    | Some (mkf _ f) => forall a, P |-- f a -> P |-- eval t
    | None => True
    end.
  Proof.
    move: (@find_correct_push t). destruct (find t) as [[A f]|]; last done.
    move=> Hft a HPf. rewrite <-Hft. by apply lexistsR with a.
  Qed.

  Lemma sdestruct_hyp t s (G: Prop):
    match find t with
    | Some (mkf _ f) => (forall a, (f a) s -> G) -> (eval t) s -> G
    | None => True
    end.
  Proof.
    move: (@find_correct_pull t). destruct (find t) as [[A f]|]; last done.
    move=> Htf HG Ht. specialize (Htf _ Ht). destruct Htf as [a Htf]. eauto.
  Qed.

  Ltac quote_term P :=
    match P with
    | ?P1 ** ?P2 =>
        let t1 := quote_term P1 in
        let t2 := quote_term P2 in
        constr:(t_star t1 t2)
    | lexists ?f => constr:(t_ex f)
    | ?P /\\ ?Q => constr:(t_propand P Q)
    | _ => constr:(t_atom P)
    end.

  Ltac sdestruct :=
    match goal with
    | |- ?P |-- ?Q =>
        let t := quote_term P in
        apply: (@find_lhs t Q) || fail 1 "Nothing to destruct";
        cbv [eval]
    | |- _ => fail 1 "Goal is not an entailment"
    end.

  Ltac sdestruct_hyp H :=
    move: H;
    match goal with
    | |- (ILFunFrm_pred ?P) ?s -> ?G =>
        let t := quote_term P in
        apply: (@sdestruct_hyp t s G) || fail 1 "Nothing to destruct";
        cbv [eval]
    | |- _ => fail 1 "Hypothesis not of the expected form"
    end.

  Ltac ssplit :=
    match goal with
    | |- ?P |-- ?Q =>
        let t := quote_term Q in
        (* If you change "eapply" to "apply:", you will get the side side
           condition you just proved in the t_propand case as an extra
           assumption in the main goal. I'm thinking that's not usually what
           you want. *)
        eapply (@find_rhs t P) || fail 1 "Nothing to split";
        cbv [eval]
    | |- _ => fail 1 "Goal is not an entailment"
    end.

  Section Example.
    Variable P: SPred.
    Variable f: nat -> SPred.

    Example ex1: P ** (Exists x1, 0 = 1 /\\ f x1) ** (Exists x2, f (1 + x2)) |-- ltrue.
    Proof.
      sdestruct => a. sdestruct => H. sdestruct => b.
      Fail sdestruct. apply: ltrueR.
    Qed.

    Example ex2: lfalse |-- P ** (Exists x1, 0 = 0 /\\ f x1) ** (Exists x2, f (1 + x2)).
    Proof.
      ssplit. ssplit; first done. ssplit. Fail ssplit.
      instantiate (1:=0). instantiate (1:=0). done.
    Qed.
  End Example.
End Existentials.

(* This tactic pulls one existential quantifier or pure proposition out of an
   SPred entailment. It should be syntactically visible, possibly nested under
   stars. *)
Ltac sdestruct := Existentials.sdestruct.

(* This tactic removes one existential quantifier or pure proposition from the
   right-hand side of an entailment goal. Existentials get instantiated by
   metavariables (like eexists), and pure propositions are created as subgoals.
 *)
Ltac ssplit := Existentials.ssplit.

(* Iterated version of sdestruct. *)
Ltac sdestructs :=
  sdestruct; let x := fresh "x" in move=> x; try sdestructs; move: x.

(* Iterated version of ssplit. *)
Ltac ssplits := ssplit; [..|try ssplits].

Tactic Notation "sdestruct" ":" hyp(H) := (Existentials.sdestruct_hyp H).

Module Solving.
  (* We index atoms in the environment with type idx, which is just a wrapper
     for nat. We cannot use any nat-specific functions on it, though, since
     cbv'ing these might cbv parts of the atom if that same function happens
     to be used there. The solution is to redefine such functions under a new
     name. *)
  Section Indexes.
    Definition idx := nat.

    Definition eqn' (i j: idx) := Eval red in eqn i j.

    Lemma eqn'P i j : reflect (i = j) (eqn' i j).
    Proof. apply eqnP. Qed.

    Definition LOOKUP_FAILURE {T} {x : T} := x.
  End Indexes.

  Inductive term :=
  | t_atom (i: idx)
  | t_star (t1 t2: term)
  | t_propand (i: idx) (t: term)
  | t_emp
  | t_false.

  (* Idea: reflect lhs first and choose index for each rhs term with a hole to
     be the first lhs atom that unifies. *)

  Definition spred_alist := seq (idx * SPred).
  Definition prop_alist := seq (idx * Prop).
  Definition env := (idx * spred_alist * prop_alist)%type.

  Fixpoint spred_lookup (a: spred_alist) (i: idx) : SPred :=
    match a with
    | (j,P) :: a' => if eqn' i j then P else spred_lookup a' i
    | [::] => @LOOKUP_FAILURE _ empSP (* default value; shouldn't happen *)
    end.

  Fixpoint prop_lookup (a: prop_alist) (i: idx) : Prop :=
    match a with
    | (j,P) :: a' => if eqn' i j then P else prop_lookup a' i
    | [::] => @LOOKUP_FAILURE _ False (* default value; shouldn't happen *)
    end.

  Fixpoint eval (e: env) (t: term) : SPred :=
    match t with
    | t_atom i => let: (_, a, _) := e in spred_lookup a i
    | t_star t1 t2 => eval e t1 ** eval e t2
    | t_propand i t => (let: (_, _, a) := e in prop_lookup a i) /\\ eval e t
    | t_emp => empSP
    | t_false => lfalse
    end.

  (* Inserts an SPred into an environment. Calls its continuation with the
     updated environment and the index where the predicate was inserted. *)
  Definition spred_insert (e: env) (P: SPred) : env * idx :=
    match e with
      | (i, a, a') => ((i.+1, (i,P)::a, a'), i)
    end.
  Ltac spred_insert_tac e(*:env*) P(*:SPred*) cont(*: env -> idx -> tactic *) :=
    let e'i := constr:(spred_insert e P) in
    let e' := (eval hnf in e'i.1) in
    let i := (eval hnf in e'i.2) in
    cont e' i.

  Definition prop_insert (e: env) (P: Prop) : env * idx :=
    match e with
      | (i, a, a') => ((i.+1, a, (i,P)::a'), i)
    end.
  Ltac prop_insert_tac e(*:env*) P(*:Prop*) cont(*: env -> idx -> tactic *) :=
    let e'i := constr:(prop_insert e P) in
    let e' := (eval hnf in e'i.1) in
    let i := (eval hnf in e'i.2) in
    cont e' i.

  (* Quote left-hand side of entailment. Duplicated terms don't get to share
     indices since this should not typically happen. *)
  (* This tactic is in CPS style to be consistent with rquote and because it
     "returns" both an updated environment and a quoted term. Ltac doesn't make
     it easy to return tuples, but CPS is easy. *)
  Ltac lquote e(*:env*) P(*:SPred*) cont(*: env -> term -> tactic *) :=
    idtac;
    lazymatch P with
    | ?P1 ** ?P2 =>
        lquote e P1 ltac:(fun e t1 =>
        lquote e P2 ltac:(fun e t2 =>
        cont e (t_star t1 t2)))
    | ?P /\\ ?T
      => prop_insert_tac e P ltac:(fun e p =>
         lquote e T ltac:(fun e t =>
         cont e (t_propand p t)))
    | lfalse => cont e t_false
    | empSP => cont e t_emp
    | _ => spred_insert_tac e P ltac:(fun e i => cont e (t_atom i))
    end.

  (*
  Goal forall P: SPred, True.
    move=> P.
    lquote ((0, [::], [::]) : env) (P ** empSP ** P ** lpropand (0 + 0 = 0) empSP) ltac:(fun e t =>
      idtac e; idtac t;
      let P := eval cbv [eval spred_lookup prop_lookup eqn'] in (eval e t) in idtac P
    ).
    apply I. Qed.
  *)

  (* Succeed iff t fails or completely solves the goal *)
  Tactic Notation "not" tactic1(t) := try (t; fail 1).

  (* This tactic succeeds if its two arguments are equal modulo alpha conversion
     and evars. As a side effect, those evars get instantiated. The power and
     complexity of this tactic falls somewhere between the built-in [constr_eq]
     and [unify] tactics. *)
  (* The programming pattern here with match/first/fail is an attempt to
     emulate if/then/else in Ltac. The first/fail pattern serves to prevent
     automatic back-tracking, analogous to "cut" in Prolog. *)
  Ltac cheap_unify p :=
    match p with
    | (?a,?b) => is_evar a; first [unify a b | fail 1]
    | (?a,?b) => is_evar b; first [unify a b | fail 1]
    | (?a,?b) => not (has_evar a); not (has_evar b); first [constr_eq a b | fail 1]
    | (?fa ?xa,?fb ?xb) => cheap_unify (fa, fb); cheap_unify (xa, xb)
    end.

  (* This looks up P in the range of the association list a and calls the
     appropriate continuation. It will look for P modulo instantiation of evars
     inside P and a. *)
  Ltac lookup_tac doUnify a(*:alist*) P(*:SPred*)
      found(*: idx -> tactic*) notfound(*: unit -> tactic*) :=
    match eval hnf in a with
    | (?i, ?P') :: _ =>
      (* We don't unify with something that's entirely an evar. This would lead
         to very random behaviour. *)
      not (is_evar P'); doUnify (P, P'); found i
    | _ :: ?a' => lookup_tac doUnify a' P found notfound
    | _ => notfound tt
    end.

  (* Quote right-hand side of entailment. Any atoms that are already in the env
     will be re-used. Existential metavariables will be instantiated greedily
     to match atoms in env. *)
  (* This tactic has to be in CPS because it refers to lookup_tac, which calls
     the [unify] tactic (https://github.com/coq/coq/commit/18e6108339aaf18499).
   *)
  Ltac rquote doUnify e(*:env*) P(*:SPred*) cont(*: env -> term -> tactic *) :=
    idtac;
    lazymatch P with
    | ?P1 ** ?P2 =>
        rquote doUnify e P1 ltac:(fun e t1 =>
        rquote doUnify e P2 ltac:(fun e t2 =>
        cont e (t_star t1 t2)))
    | ?P /\\ ?T =>
        rquote doUnify e T ltac:(fun e t =>
          let a' := match e with (_, ?a, ?a') => constr:(a') end in
          lookup_tac doUnify a' P
            ltac:(fun j => cont e (t_propand j t))
            ltac:(fun _ => prop_insert_tac e P ltac:(fun e i => cont e (t_propand i t))))
    | empSP => cont e t_emp
    | lfalse => cont e t_false
    | ltrue =>
          (* We don't match up ltrue. We leave it untouched on the right-hand
             side and let the user decide what to do with it. *)
           spred_insert_tac e P ltac:(fun e i => cont e (t_atom i))
    | _ => first [ is_evar P;
                   (* If an atom is entirely an evar, we don't touch it. Otherwise, it
                      would unify with the first thing it saw on the left, which is
                      probably not what the user expects. *)
                   spred_insert_tac e P ltac:(fun e i => cont e (t_atom i))
                 | idtac;
                   match e with
                     | (_, ?a, ?a') =>
                       lookup_tac doUnify a P
                         ltac:(fun j => cont e (t_atom j))
                         ltac:(fun _ => spred_insert_tac e P ltac:(fun e i => cont e (t_atom i)))
                   end ]
    end.

  (** Remove one instance of the atom with index [i] *)
  Fixpoint remove_atom t i : option term :=
    match t with
    | t_atom i' => if eqn' i' i then Some t_emp else None
    | t_star t1 t2 =>
        match remove_atom t1 i with
        | Some t1' => Some (t_star t1' t2)
        | None =>
            match remove_atom t2 i with
            | Some t2' => Some (t_star t1 t2')
            | None => None
            end
        end
    | t_propand P t' =>
      match remove_atom t' i with
        | Some t'' => Some (t_propand P t'')
        | None => None
      end
    | t_emp => None
    | t_false => None
    end.

  (** Remove all instances of the prop with index [i] *)
  Fixpoint remove_prop t i : option term :=
    match t with
    | t_atom i' => None
    | t_star t1 t2 =>
        match remove_prop t1 i, remove_prop t2 i with
        | Some t1', Some t2' => Some (t_star t1' t2')
        | Some t1', None => Some (t_star t1' t2)
        | None, Some t2' => Some (t_star t1 t2')
        | None, None => None
        end
    | t_propand p t' => if eqn' p i
                        then match remove_prop t' i with
                               | Some t'' => Some t''
                               | None => Some t'
                             end
                        else None
    | t_emp => None
    | t_false => None
    end.

  (** Remove all terms showing up in [tQ] from [tP]. *)
  Fixpoint remove (tP tQ: term) : option term :=
    match tQ with
    | t_atom i => remove_atom tP i
    | t_star t1 t2 =>
        match remove tP t1 with
        | Some tP' => remove tP' t2
        | None => None
        end
    | t_propand P t =>
        match remove tP t with
        | Some tP' => remove_prop tP' P
        | None => None
        end
    | t_emp => Some tP
    | t_false => None
    end.

  Local Ltac cancel_sepSP :=
    idtac;
    match goal with
      | [ |- ?a ** ?b |-- ?a ** ?b' ] => (f_cancel; [])
      | [ |- ?a ** ?b |-- ?a' ** ?b ] => (f_cancel; [])
      | [ |- ?a ** ?b -|- ?a ** ?b' ] => (f_cancel; [])
      | [ |- ?a ** ?b -|- ?a' ** ?b ] => (f_cancel; [])
    end.

  Local Ltac t_septac' :=
    idtac;
    match goal with
      | _ => reflexivity
      | _ => eassumption
      | _ => progress simpl_paths
      | _ => progress subst
      | _ => progress simpl
      | _ => progress rewrite ?eq_refl ?empSPL ?empSPR ?sepSPA
      | _ => progress setoid_rewrite <- bilpropandL
      | _ => progress setoid_rewrite <- bilpropandR
      | _ => rewrite ?sepSPA; progress cancel_sepSP
      | _ => rewrite -?sepSPA; progress cancel_sepSP
      | _ => progress destruct_head ex
      | _ => progress destruct_head and
      | [ H : eval _ _ -|- _ |- _ ] => setoid_rewrite -> H; clear H
      | [ H : context[?a == ?a] |- _ ] => rewrite eq_refl in H
      | [ H : context[eqn' ?a ?b] |- _ ] => change (eqn' a b) with (a == b) in *; case_eq (a == b) => *
      | [ H : (?a == ?b) = _, H' : context[?a == ?b] |- _ ] => rewrite H in H'
      | [ H : (?a == ?b) = true |- _ ] => move/eqP in H
      | [ |- _ /\\ _ |-- _ ] => apply lpropandL => *
      | [ |- _ |-- _ /\\ _ ] => (apply lpropandR; try assumption)
      | [ H : forall _, Some _ = Some _ -> _ |- _ ] => specialize (H _ (reflexivity _))
      | [ H : forall _, None = Some _ -> _ |- _ ] => clear H
      | [ H : forall _ _, (_, _) = (_, _) -> _ |- _ ] => specialize (H _ _ (reflexivity _))
      | [ |- ?a ** ?b -|- ?b ** ?a ] => by rewrite sepSPC
      | [ |- _ /\\ _ |-- _ ] => apply lpropandL => *
      | [ |- _ |-- _ /\\ _ ] => (apply lpropandR; first by eassumption)
    end.

  Local Ltac t_remove' :=
    idtac;
    match goal with
      | _ => t_septac'
      | [ H : context[match remove_prop ?a ?b with _ => _ end] |- _ ]
        => (destruct (remove_prop a b); try done)
      | [ H : context[remove_atom ?a ?b] |- _ ]
        => (destruct (remove_atom a b); try done)
    end.

  Local Ltac t_remove := do ?[ t_remove' | split; by t_remove ].

  Lemma remove_atom_correct e t i tR:
    remove_atom t i = Some tR ->
    eval e t -|- eval e (t_atom i) ** eval e tR.
  Proof.
    move: tR.
    (elim: t => /= *; try done);
      t_remove.
  Qed.

  Lemma remove_prop_correct e t i tR:
    remove_prop t i = Some tR ->
    eval e t -|- eval e (t_propand i tR).
  Proof.
    move: tR.
    (elim: t => /= *; try done);
      t_remove.
  Qed.

  Lemma remove_correct e tP tQ tR:
    remove tP tQ = Some tR ->
    eval e tP -|- eval e tQ ** eval e tR.
  Proof.
    move: tP tR. elim: tQ.
    { move=> i tP tR /= HtR. exact: remove_atom_correct. }
    { move=> t1 IHt1 t2 IHt2 tP tR /=.
      specialize (IHt1 tP).
      destruct (remove tP t1) as [tP'|]; last done.
      move=> HtR. move/(_ _ _ HtR): IHt2 => Ht2.
      rewrite sepSPA. rewrite <-Ht2. exact: IHt1. }
    { move => /= i t IH tP *.
      specialize (IH tP).
      destruct (remove tP t); last by exfalso.
      rewrite -> IH; clear IH; last by reflexivity.
      let H := match goal with | [ H : remove_prop ?a ?b = Some _ |- _ ] => constr:(H) end in
      rewrite -> (@remove_prop_correct _ _ _ _ H).
      by do ![ progress simpl
             | progress setoid_rewrite <- bilpropandL
             | progress setoid_rewrite <- bilpropandR ]. }

    { move=> tP tR /= [<-]. by rewrite empSPL. }

    { move=> tP tR /=. done. }
  Qed.

  (** We have the option to remove matched [Prop] bits from the
      hypotheses; we choose not to do so.  We treat [tH] as the
      hypotheses and [tC] as the conclusions. *)
  Fixpoint simplify (tC tH: term) : (term * term) :=
    match tH with
    | t_atom i =>
        match remove_atom tC i with
        | Some tC' => (tC', t_emp)
        | None => (tC, tH)
        end
    | t_star t1 t2 =>
        let (tC', t1')  := simplify tC t1 in
        let (tC'', t2') := simplify tC' t2 in
        (tC'', t_star t1' t2')
    | t_propand P t =>
        let (tC', t') := eta_expand (simplify tC t) in
        match remove_prop tC' P with
          | Some tC'' => (tC'', t_propand P t')
          | None => (tC', t_propand P t')
        end
    | t_emp => (tC, tH)
    | t_false => (tC, tH)
    end.

  Local Ltac t_simplify_correct' :=
    idtac;
    match goal with
      | [ e : env, H : context[match remove_atom ?a ?b with _ => _ end] |- _ ]
        => pose proof (@remove_atom_correct e a b); destruct (remove_atom a b)
      | [ e : env, H : context[match remove_prop ?a ?b with _ => _ end] |- _ ]
        => pose proof (@remove_prop_correct e a b); destruct (remove_prop a b)
      | _ => t_septac'
    end.

  Local Ltac t_simplify_correct :=
    do ![ t_simplify_correct'
        | eexists (t_propand _ _); by t_simplify_correct
        | eexists (t_star _ _); by t_simplify_correct
        | eexists (t_atom _); by t_simplify_correct
        | exists t_emp; by t_simplify_correct
        | eexists; by t_simplify_correct
        | split; by t_simplify_correct ].

  (* Correctness theorem strong enough for induction. *)
  Lemma simplify_correct e tH tC tH' tC' :
    simplify tC tH = (tC', tH') -> exists tR,
    (eval e tH -|- eval e tH' ** eval e tR)  /\
    (eval e tC -|- eval e tC' ** eval e tR).
  Proof.
    move: tC tC' tH'.
    elim: tH.
    { move => /= *; t_simplify_correct. }
    { move=> t1 IHt1 t2 IHt2 tC tC'' tH' /=.
      specialize (IHt1 tC). destruct (simplify tC t1) as [tC' t1'].
      specialize (IHt2 tC'). destruct (simplify tC' t2) as [ttmp t2'].
      move=> [Htmp <-] /=. subst ttmp.
      edestruct IHt1 as [tR1 [Hpre1 Hpost1]]; first reflexivity.
      edestruct IHt2 as [tR2 [Hpre2 Hpost2]]; first reflexivity.
      clear IHt1 IHt2. exists (t_star tR1 tR2) => /=.
      t_simplify_correct. }
    { move => /= P t IH tC *.
      have Hprop := @remove_prop_correct e (simplify tC t).1 P.
      specialize (IH tC _ _ (prod_eta _ _ _)).
      edestruct remove_prop; simpl_paths; subst;
      (specialize (Hprop _ (reflexivity _)) || clear Hprop);
      t_simplify_correct. }
    { move=> tP tP' tQ' /= [<- <-]. exists t_emp.
      rewrite !empSPR. split; reflexivity. }
    { move=> tP tP' tQ' /= [<- <-]. exists t_emp.
      rewrite !empSPR. split; reflexivity. }
  Qed.

  (* Weaker version of correctness theorem. *)
  Corollary simplify_sufficient e tH tC tH' tC' :
    simplify tC tH = (tC', tH') ->
    eval e tH' |-- eval e tC'  ->  eval e tH |-- eval e tC.
  Proof.
    move=> Heq H. have [tR [H1 H2]] := simplify_correct e Heq.
    rewrite ->H1, ->H2. by f_cancel.
  Qed.

  (* remove emp, pull false *)
  Fixpoint clean t :=
    match t with
    | t_star t1 t2 =>
        let t1' := clean t1 in
        let t2' := clean t2 in
        match t1', t2' with
        | t_false, t' => t_false
        | t', t_false => t_false
        | t_emp, t' => t'
        | t', t_emp => t'
        | _, _ => t_star t1' t2'
        end
    | t_propand P t' =>
        let t'' := clean t' in
        match t'' with
          | t_false => t_false
          | _ => t_propand P t''
        end
    | _ => t
    end.

  Lemma clean_correct e t : eval e (clean t) -|- eval e t.
  Proof.
    induction t; try reflexivity.
    { rewrite /=.
      destruct (clean t1); destruct (clean t2); rewrite -IHt1 -IHt2;
      try rewrite empSPL; try rewrite empSPR;
      try rewrite sepSP_falseL; try rewrite sepSP_falseR; reflexivity. }
    { simpl; destruct (clean t); simpl in *; rewrite <- IHt; try reflexivity.
      split; do ?[ reflexivity
                 | apply lfalseL
                 | apply lpropandL ]. }
  Qed.

  (** bring lpropand to the top *)
  (** I'm lazy, so I'll just count how many t_propands there are, and give the procedure that much fuel *)
  Definition addn' := Eval lazy in addn.
  Fixpoint count_t_propand t :=
    match t with
      | t_star t1 t2 => addn' (count_t_propand t1) (count_t_propand t2)
      | t_propand _ t' => (count_t_propand t').+1
      | _ => 0
    end.

  Fixpoint pull1_t_propand t :=
    match t with
      | t_star t1 t2
        => let t1' := pull1_t_propand t1 in
           let t2' := pull1_t_propand t2 in
           match t1', t2' with
             | t_propand P1 t1'', t_propand P2 t2'' => t_propand P1 (t_propand P2 (t_star t1'' t2''))
             | t_propand P t1'', t2'' => t_propand P (t_star t1'' t2'')
             | t1'', t_propand P t2'' => t_propand P (t_star t1'' t2'')
             | t1'', t2'' => t_star t1'' t2''
           end
      | t_propand P t' => t_propand P (pull1_t_propand t')
      | _ => t
    end.

  Fixpoint rep {T} (f : T -> T) x n :=
    if n is n.+1 then f (rep f x n) else x.

  Definition pull_t_propand t := rep pull1_t_propand t (count_t_propand t).

  Lemma pull1_t_propand_correct e t : eval e (pull1_t_propand t) -|- eval e t.
  Proof.
    induction t; try reflexivity;
    simpl; do !hyp_rewrite <- *; clear; try reflexivity.
    do 2 edestruct pull1_t_propand;
      do ![ reflexivity
          | progress setoid_rewrite <- bilpropandL
          | progress setoid_rewrite <- bilpropandR ].
  Qed.

  Lemma pull_t_propand_correct e t : eval e (pull_t_propand t) -|- eval e t.
  Proof.
    unfold pull_t_propand.
    generalize (count_t_propand t) => n.
    move: t.
    induction n => * //=.
    by rewrite -> pull1_t_propand_correct.
  Qed.

  Lemma do_simplify e tH tC tH' tC':
    simplify tC tH = (tC', tH') ->
    eval e (clean (pull_t_propand tH')) |-- eval e (clean (pull_t_propand tC'))  ->  eval e tH |-- eval e tC.
  Proof. rewrite !clean_correct !pull_t_propand_correct. apply simplify_sufficient. Qed.

  (* If speed is an issue at some point, we could make rquote take two
     environments: one to insert into and one to lookup in. Our decision
     procedures never care about duplicated atoms on either side -- only atoms
     in common between left and right.

     We first try to do unification up to syntax, and try again after we've simpled *)
  Ltac pre_ssimpl_with doUnify :=
    first [ syntax_unify_reflexivity
          | match goal with
              | [ |- ?P |-- ?Q ] =>
                lquote ((0, [::], [::]) : env) P ltac:(fun e tP =>
                  rquote doUnify e Q ltac:(fun e tQ =>
                    eapply (@do_simplify e tP tQ);
                    [ cbv; reflexivity
                    | cbv [eval spred_lookup prop_lookup eqn' clean pull_t_propand pull1_t_propand rep count_t_propand addn']
                    ]
                  )
                )
            end;
            try syntax_unify_reflexivity ].

  (** After we're done, we want to move the things involving
      [lpropand] in the hypothesis list into the Coq context.  They're
      all at the top, so we can just apply [lpropandL] repeatedly. *)
  Ltac post_ssimpl :=
    repeat match goal with
             | [ |- _ /\\ _ |-- _ ] => apply lpropandL => *
             | [ H : ?T |- _ |-- ?T /\\ _ ] => apply lpropandR; first by exact H
           end.

  Ltac ssimpl_with doUnify := pre_ssimpl_with doUnify; post_ssimpl.

  Ltac ssimpl := ssimpl_with cheap_unify.

  Example ex0: forall P Q: SPred, exists n,
        ltrue ** (1 = 1 /\\ empSP) ** P ** Q |-- (Q ** (n = 1 /\\ empSP)) ** ltrue.
  Proof. move=> P Q. eexists. ssimpl. done. Qed.

  (* TODO: probably subsumed by do_simplify, but this should be faster *)
  Lemma solve_uc e tH tC:
    if remove tH tC is Some _
    then eval e tH |-- eval e tC ** ltrue
    else True.
  Proof.
    move Hresult: (remove tH tC) => result.
    destruct result; last done.
    have Hcorrect := remove_correct e Hresult.
    rewrite -> Hcorrect. by f_cancel.
  Qed.

  Ltac solve_uc :=
    match goal with
    |- ?P |-- ?Q ** ltrue =>
        lquote ((0, [::], [::]) : env) P ltac:(fun e tP =>
          rquote cheap_unify e Q ltac:(fun e tQ =>
            apply (@solve_uc e tP tQ)
          )
        )
    end.

  Example ex1: forall P Q: SPred, exists n,
        (1 = 1 /\\ empSP) ** P ** Q |-- (Q ** (n = 1 /\\ empSP)) ** ltrue.
  Proof. move=> P Q. eexists. solve_uc. Qed.
End Solving.

Ltac ssimpl := Solving.ssimpl.
Ltac ssimpl_with := Solving.ssimpl_with.


Ltac sbazookaone_with PT :=
  (try sdestructs => * //; (* leaves 0 or 1 subgoal *)
  try ssplits; (* last subgoal is the entailment *)
  [..| done || (try (ssimpl_with PT))] => //).

Ltac sbazookaonealt_with PT :=
  (* First try and prove from lfalseL *)
  try (ssimpl_with PT);
  match goal with
  | |- lfalse |-- ?Q => apply lfalseL
  | |- ?P /\\ lfalse |-- ?Q => (apply lpropandL => _; apply lfalseL)
  | _ => sbazookaone_with PT
  end.

(** Overpowered super-tactic *)
(** Include [idtac;] so that if we pass [sbazooka] as an argument to a
    tactical, it doesn't immediately evaluate the [match] and complain
    that there are no matching goals. *)
Ltac sbazooka_with PT :=
    idtac;
    match goal with
    | |- ?P -|- ?Q => (split; sbazookaonealt_with PT)
    | |- _ => sbazookaonealt_with PT
    end.

Ltac sbazooka := sbazooka_with Solving.cheap_unify.
