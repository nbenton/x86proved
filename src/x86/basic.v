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
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.spectac x86proved.safe x86proved.pointsto x86proved.cursor x86proved.reader.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.

Section Basic.
  (** Basic block of position-independent code *)
  Context {T} `{MI: MemIs T}.

  Definition basic P (c : T) Q : spec :=
    Forall (i j : DWORD),
    (safe @ (EIP ~= j ** Q) -->> safe @ (EIP ~= i ** P)) @ (i -- j :-> c).

  Global Strategy 10000 [basic].

  (* Push spec through basic *)
  Lemma spec_at_basic P c Q R :
    basic P c Q @ R -|- basic (P ** R) c (Q ** R).
  Proof.
    rewrite /basic.
    repeat match goal with
             | [ |- Forall _ : ?T, _ -|- Forall _ : ?T, _ ] => cancel1 => ?
             | _ => progress autorewrite with push_at
           end.
    rewrite (sepSPC _ R). by rewrite -4!sepSPA. 
  Qed.

  (* We need to rewrite with [spec_at_basic] so much in applying
     instrrules that it's worth creating a specialized version for use
     in rewriting.  Rewriting with this one is about twice as fast as
     rewriting with the other one. *)
  Lemma spec_at_basic_directionalized1 P c Q R :
    basic (P ** R) c (Q ** R) |-- basic P c Q @ R.
  Proof.
    exact (proj2 (@spec_at_basic P c Q R)).
  Qed.

  Lemma spec_at_basic_directionalized2 P c Q R :
    basic P c Q @ R |-- basic (P ** R) c (Q ** R).
  Proof.
    exact (proj1 (@spec_at_basic P c Q R)).
  Qed.

  (* Frame rule for Hoare triples *)
  Lemma basic_frame R S P c Q :
    S |-- basic P c Q ->
    S |-- basic (P ** R) c (Q ** R).
  Proof. by rewrite <-spec_at_basic, <-spec_frame. Qed.

  (* Rule of consequence *)
  Lemma basic_roc P' Q' S P c Q:
    P |-- P' ->
    Q' |-- Q ->
    S |-- basic P' c Q' ->
    S |-- basic P c Q.
  Proof.
    move=> HP HQ H. rewrite /basic in H.
    setoid_rewrite <-HP in H. setoid_rewrite ->HQ in H. 
    apply H.
  Qed.

  (* Morphisms for triples *)
  Global Instance basic_entails_m:
    Proper (lentails --> eq ==> lentails ++> lentails) basic.
  Proof.
    move => P P' HP c _ <- Q Q' HQ. apply: basic_roc; try eassumption.
    done.
  Qed.

  Global Instance basic_equiv_m:
    Proper (lequiv ==> eq ==> lequiv ==> lequiv) basic.
  Proof.
    split; apply basic_entails_m. apply H. done. apply H1. apply H. done.
    apply H1. 
  Qed.

  (* Annoying extra instances to work around a bug with setoid rewriting on the
     fourth argument in the general morphism above *)
  Global Instance basic_entails_m' P c:
    Proper (eq ==> lentails) (basic P c).
  Proof.
    repeat move => *. subst; apply: basic_roc; try eassumption. done. reflexivity. done.
  Qed.

  Global Instance basic_equiv_m' P c:
    Proper (lequiv ==> lequiv) (basic P c).
  Proof.
    move => Q Q' HQ. split. by setoid_rewrite HQ.
      by setoid_rewrite <-HQ.
  Qed.

  (* Special case of consequence for precondition *)
  Lemma basic_roc_pre P' S P c Q:
    P |-- P' ->
    S |-- basic P' c Q ->
    S |-- basic P c Q.
  Proof. move=> HP H. by rewrite ->HP. Qed.

  (* Special case of consequence for postcondition *)
  Lemma basic_roc_post Q' S P c Q:
    Q' |-- Q ->
    S |-- basic P c Q' ->
    S |-- basic P c Q.
  Proof. move=> HQ H. by rewrite <- HQ. Qed.

  Lemma basic_exists A S P c Q:
    (forall a:A, S |-- basic (P a) c Q) ->
    S |-- basic (lexists P) c Q.
  Proof. rewrite /basic => H. specintros => *. eforalls H. simple apply H. Qed.

  Lemma basic_post_exists A S P c Q:
    (S |-- Exists a : A, basic P c (Q a)) ->
    S |-- basic P c (lexists Q).
  Proof.
    rewrite /basic => H. rewrite -> H; clear H.
    repeat match goal with
             | [ |- lexists _ |-- _ ] => apply lexistsL => ?
             | _ => progress specintros => *
             | [ |- lforall _ |-- _ ] => eapply lforallL
             | [ |- ?f ?a |-- ?g ?b ] => unify a b; cancel2
             | [ |- ?f _ |-- ?g _ ] => unify f g; cancel1
             | [ |- _ |-- lexists _ ] => eapply lexistsR
           end. 
  Qed.

  Global Instance AtEx_basic P c Q : AtEx (basic P c Q).
  Proof. rewrite /basic. apply AtEx_forall => i.
         apply AtEx_forall => j. apply _. Qed.

  Lemma basic_basic_context R S' P' Q' S P c Q:
    S' |-- basic P' c  Q' ->
    S |-- S' ->
    P |-- P' ** R ->
    Q' ** R |-- Q ->
    S |-- basic P c Q.
  Proof. move=> Hc HS HP HQ. apply: basic_roc. apply HP. apply HQ. rewrite -> HS. exact: basic_frame. Qed.

  (* Combine rule of consequence and frame *)
  Lemma basic_basic R P' Q' S P c Q:
    |-- basic P' c Q' ->
    P |-- P' ** R ->
    Q' ** R |-- Q ->
    S |-- basic P c Q.
  Proof.
    move=> Hc HP HQ. apply: basic_basic_context; try eassumption. done. 
  Qed.

  Lemma basic_safe_context P P' Q' R S' S c (i j: DWORD):
    S' |-- basic P' c Q' ->
    S |-- S' ->
    (* The order of separating conjuncts in the following premise is crucial for
       allowing ssimpl to solve it in practice. *)
    P |-- EIP ~= i ** i -- j :-> c ** P' ** R ->
    S |-- safe @ (Q' ** EIP ~= j ** i -- j :-> c ** R) ->
    S |-- safe @ P.
  Proof.
    move=> Hbasic HS' HP HS.
    lforwardR Hbasic.
    - apply lforallL with i. apply lforallL with j. apply (spec_frame R).
    rewrite ->spec_at_at in Hbasic.
    safeapply Hbasic.
    - rewrite ->HP. by ssimpl.
    - rewrite ->HS. autorewrite with push_at. cancel1. by ssimpl.
  Qed.

  Lemma basic_safe P P' Q' R S (c: T) (i j: DWORD):
    |-- basic P' c Q' ->
  (* The order of separating conjuncts in the following premise is crucial for
     allowing ssimpl to solve it in practice. *)
  P |-- EIP ~= i ** i -- j :-> c ** P' ** R ->
  S |-- safe @ (Q' ** EIP ~= j ** i -- j :-> c ** R) ->
  S |-- safe @ P.
  Proof.
    move=> Hbasic HP HS. eapply (basic_safe_context); try eassumption.
    done.
  Qed.

End Basic.

Hint Rewrite @spec_at_basic @spec_at_basic : push_at.



Hint Unfold basic : specapply.

Module Export Existentials_basic.
  Import Existentials.

  Lemma pq_basic {M} {HM: MemIs M} t c Q:
    match find t with
    | Some (mkf _ f) =>
        PullQuant (@basic _ HM (eval t) c Q) (fun a => @basic _ HM (f a) c Q)
    | None => True
    end.
  Proof.
    move: (@find_correct_pull t). case: (find t) => [[A f]|]; last done.
    red. move=> Heval. rewrite ->Heval.
    apply basic_exists => a. by apply lforallL with a.
  Qed.

  Hint Extern 0 (PullQuant (@basic ?M ?HM ?P ?c ?Q) _) =>
    let t := quote_term P in
    apply (@pq_basic M HM t c Q) : pullquant.

End Existentials_basic.