(*===========================================================================
  Definition of Hoare triple for arbitrary code-like data
  For store assertions P and Q and "code" c, we write
     basic P c Q
  to mean
     for any addresses i and j that point to code c,
     if   it's safe to run from EIP=j with assertion Q
     then it's safe to run from EIP=i with assertion P
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.opred x86proved.spec x86proved.spectac x86proved.safe x86proved.obs x86proved.cursor x86proved.x86.instr x86proved.reader x86proved.x86.instrcodec x86proved.x86.eval.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.

Section Basic.
  (** Basic block of position-independent code *)
  (** We have two variants, one for loopy (potentially
      non-terminating) code, and one for loopless code.  For
      non-terminating code, we want to say that if it's fine if we
      crash after ∞ steps.  But [catOP] says that if there is no valid
      output at infinity, we are already doomed.  We combine them into
      something that has a projection to [OPred]s. *)
  Context {T_OPred} {proj : T_OPred -> OPred}.
  Local Coercion proj : T_OPred >-> OPred.

  Context {T} `{MI: MemIs T}.

  Definition parameterized_basic P (c : T) (O : OPred) Q : spec :=
    Forall (i j : ADDR) (O' : T_OPred),
    (obs O' @ (UIP ~= j ** Q) -->> obs (catOP O O') @ (UIP ~= i ** P)) <@ (i -- j :-> c).

  Global Strategy 10000 [parameterized_basic].

  (* Push spec through basic *)
  Lemma spec_at_basic P c O Q R :
    parameterized_basic P c O Q @ R -|- parameterized_basic (P ** R) c O (Q ** R).
  Proof.
    rewrite /parameterized_basic.
    repeat match goal with
             | [ |- Forall _ : ?T, _ -|- Forall _ : ?T, _ ] => cancel1 => ?
             | _ => progress autorewrite with push_at
           end.
      by rewrite -2!sepSPA.
  Qed.

  (* We need to rewrite with [spec_at_basic] so much in applying
     instrrules that it's worth creating a specialized version for use
     in rewriting.  Rewriting with this one is about twice as fast as
     rewriting with the other one. *)
  Lemma spec_at_basic_directionalized1 P c O Q R :
    parameterized_basic (P ** R) c O (Q ** R) |-- parameterized_basic P c O Q @ R.
  Proof.
    exact (proj2 (@spec_at_basic P c O Q R)).
  Qed.

  Lemma spec_at_basic_directionalized2 P c O Q R :
    parameterized_basic P c O Q @ R |-- parameterized_basic (P ** R) c O (Q ** R).
  Proof.
    exact (proj1 (@spec_at_basic P c O Q R)).
  Qed.

  (* Frame rule for Hoare triples *)
  Lemma basic_frame R S P c O Q :
    S |-- parameterized_basic P c O Q ->
    S |-- parameterized_basic (P ** R) c O (Q ** R).
  Proof. by rewrite <-spec_at_basic, <-spec_frame. Qed.

  (* Rule of consequence *)
  Lemma basic_roc P' O' Q' S P c O Q:
    P |-- P' ->
    Q' |-- Q ->
    O' |-- O ->
    S |-- parameterized_basic P' c O' Q' ->
    S |-- parameterized_basic P c O Q.
  Proof.
    move=> HP HQ HO H. rewrite /parameterized_basic in H.
    setoid_rewrite <-HP in H. setoid_rewrite ->HQ in H.  setoid_rewrite ->HO in H.
    apply H.
  Qed.

  (* Morphisms for triples *)
  Global Instance basic_entails_m:
    Proper (lentails --> eq ==> lentails ++> lentails ++> lentails) parameterized_basic.
  Proof.
    move => P P' HP c _ <- O O' HO Q Q' HQ. apply: basic_roc; try eassumption.
    done.
  Qed.

  Global Instance basic_equiv_m:
    Proper (lequiv ==> eq ==> lequiv ==> lequiv ==> lequiv) parameterized_basic.
  Proof.
    split; apply basic_entails_m. apply H. done. apply H1. apply H2. apply H. done.
    apply H1. apply H2.
  Qed.

  (* Annoying extra instances to work around a bug with setoid rewriting on the
     fourth argument in the general morphism above *)
  Global Instance basic_entails_m' P c:
    Proper (eq ==> lentails ++> lentails) (parameterized_basic P c).
  Proof.
    repeat move => *. subst; apply: basic_roc; try eassumption. done. reflexivity. done.
  Qed.

  Global Instance basic_entails_m'' P c O :
    Proper (Basics.flip lentails ++> Basics.flip lentails) (parameterized_basic P c O).
  Proof.
    move => Q Q' H. apply: basic_roc. done. apply H. reflexivity. done.
  Qed.

  Global Instance basic_equiv_m' P c:
    Proper (lequiv ==> lequiv ==> lequiv) (parameterized_basic P c).
  Proof.
    move => O O' HO Q Q' HQ. setoid_rewrite HO. split. by setoid_rewrite HQ.
      by setoid_rewrite <-HQ.
  Qed.

  (* Special case of consequence for precondition *)
  Lemma basic_roc_pre P' S P c O Q:
    P |-- P' ->
    S |-- parameterized_basic P' c O Q ->
    S |-- parameterized_basic P c O Q.
  Proof. move=> HP H. by rewrite ->HP. Qed.

  (* Special case of consequence for postcondition *)
  Lemma basic_roc_post Q' S P c O Q:
    Q' |-- Q ->
    S |-- parameterized_basic P c O Q' ->
    S |-- parameterized_basic P c O Q.
  Proof. move=> HQ H. by rewrite <- HQ. Qed.

  Lemma basic_exists A S P c O Q:
    (forall a:A, S |-- parameterized_basic (P a) c O Q) ->
    S |-- parameterized_basic (lexists P) c O Q.
  Proof. rewrite /parameterized_basic => H. specintros => *. eforalls H. simple apply H. Qed.

  Lemma basic_post_exists A S P c O Q:
    (S |-- Exists a : A, parameterized_basic P c O (Q a)) ->
    S |-- parameterized_basic P c O (lexists Q).
  Proof.
    rewrite /parameterized_basic => H. rewrite -> H; clear H.
    repeat match goal with
             | [ |- lexists _ |-- _ ] => apply lexistsL => ?
             | _ => progress specintros => *
             | [ |- lforall _ |-- _ ] => eapply lforallL
             | [ |- ?f ?a |-- ?g ?b ] => unify a b; cancel2
             | [ |- ?f _ |-- ?g _ ] => unify f g; cancel1
             | [ |- _ |-- lexists _ ] => eapply lexistsR
           end. 
  Qed.

  Global Instance AtEx_basic P c O Q : AtEx (parameterized_basic P c O Q).
  Proof. rewrite /parameterized_basic. apply AtEx_forall => i.
         apply AtEx_forall => j. apply AtEx_forall => O'. apply _. Qed.

  Lemma basic_basic_context R S' P' O' Q' S P c O Q:
    S' |-- parameterized_basic P' c O' Q' ->
    S |-- S' ->
    P |-- P' ** R ->
    O' |-- O ->
    Q' ** R |-- Q ->
    S |-- parameterized_basic P c O Q.
  Proof. move=> Hc HS HP HO HQ. apply: basic_roc. apply HP. apply HQ. apply HO.
         rewrite -> HS. exact: basic_frame. Qed.

  (* Combine rule of consequence and frame *)
  Lemma basic_basic R P' Q' O S P c Q:
    |-- parameterized_basic P' c O Q' ->
    P |-- P' ** R ->
    Q' ** R |-- Q ->
    S |-- parameterized_basic P c O Q.
  Proof.
    move=> Hc HP HQ. apply: basic_basic_context; try eassumption. done. done.
  Qed.
End Basic.

Global Notation basic := (@parameterized_basic OPred (fun x => x) _ _).
Global Notation "@ 'basic'" := (@parameterized_basic OPred (fun x => x))
  (at level 10, T at level 8, only parsing).

Global Notation loopy_basic := (@parameterized_basic PointedOPred OPred_pred _ _).
Global Notation "@ 'loopy_basic'" := (@parameterized_basic PointedOPred OPred_pred)
  (at level 10, T at level 8, only parsing).

Section loopy_loopless.
  Context {T_OPred} {proj : T_OPred -> OPred}.
  Context {T} `{MI: MemIs T}.

  Lemma basic__parameterized_basic P c O Q : basic P c O Q |-- @parameterized_basic T_OPred proj _ _ P c O Q.
  Proof.
    rewrite /basic/loopy_basic/parameterized_basic.
    repeat match goal with
             | [ |- _ |-- lforall _ ] => apply lforallR => ?
           end.
    repeat match goal with
             | [ |- lforall _ |-- _ ] => eapply lforallL
           end.
    reflexivity.
  Qed.

  Lemma weaken_parameterized_basic P c O Q C : C |-- basic P c O Q -> C |-- @parameterized_basic T_OPred proj _ _ P c O Q.
  Proof.
    rewrite -> basic__parameterized_basic.
    exact id.
  Qed.
End loopy_loopless.

Hint Rewrite @spec_at_basic @spec_at_basic : push_at.

Hint Unfold parameterized_basic : specapply.

Module Export Existentials_basic.
  Import Existentials.

  Lemma pq_basic {T_OPred} {proj : T_OPred -> OPred} {M} {HM: MemIs M} t c O Q:
    match find t with
    | Some (mkf _ f) =>
        PullQuant (@parameterized_basic _ proj _ HM (eval t) c O Q) (fun a => @parameterized_basic _ proj _ HM (f a) c O Q)
    | None => True
    end.
  Proof.
    move: (@find_correct_pull t). case: (find t) => [[A f]|]; last done.
    red. move=> Heval. rewrite ->Heval.
    apply basic_exists => a. by apply lforallL with a.
  Qed.

  Hint Extern 0 (PullQuant (@parameterized_basic ?T_OPred ?proj ?M ?HM ?P ?c ?O ?Q) _) =>
    let t := quote_term P in
    apply (@pq_basic T_OPred proj M HM t c O Q) : pullquant.

End Existentials_basic.
