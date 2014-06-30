(*===========================================================================
  Definition of Hoare triple for arbitrary code-like data
  For store assertions P and Q and "code" c, we write
     basic P c Q
  to mean
     for any addresses i and j that point to code c,
     if   it's safe to run from EIP=j with assertion Q
     then it's safe to run from EIP=i with assertion P
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred OPred septac spec spectac safe obs pointsto cursor instr reader instrcodec.
Require Import Setoid RelationClasses Morphisms.

Section Basic.
  Context {T} `{MI: MemIs T}.

  (** Basic block of position-independent code *)
  Definition basic P (c:T) (O: OPred) Q : spec :=
    Forall i j:DWORD, Forall O': OPred, 
    (obs O' @ (EIP ~= j ** Q) -->> obs (catOP O O') @ (EIP ~= i ** P)) <@ (i -- j :-> c).
  Global Strategy 10000 [basic].

  (* Push spec through basic *)
  Lemma spec_at_basic P c O Q R :
    basic P c O Q @ R -|- basic (P ** R) c O (Q ** R).
  Proof.
    rewrite /basic.
    autorewrite with push_at. cancel1 => i.
    autorewrite with push_at. cancel1 => j.
    autorewrite with push_at. cancel1 => O'. 
    autorewrite with push_at. rewrite -2!sepSPA. 
    reflexivity.
  Qed.

  (* Frame rule for Hoare triples *)
  Lemma basic_frame R S P c O Q :
    S |-- basic P c O Q ->
    S |-- basic (P ** R) c O (Q ** R).
  Proof. by rewrite <-spec_at_basic, <-spec_frame. Qed.

  (* Rule of consequence *)
  Lemma basic_roc P' O' Q' S P c O Q:
    P |-- P' ->
    Q' |-- Q ->
    entailsOP O' O ->
    S |-- basic P' c O' Q' ->
    S |-- basic P c O Q.
  Proof.
    move=> HP HQ HO H. rewrite /basic in H.
    setoid_rewrite <-HP in H. setoid_rewrite ->HQ in H. setoid_rewrite ->HO in H. 
    apply H.
  Qed.

  (* Morphisms for triples *)
  Global Instance basic_entails_m:
    Proper (lentails --> eq ==> entailsOP ++> lentails ++> lentails) basic.
  Proof.
    move => P P' HP c _ <- O O' HO Q Q' HQ. apply: basic_roc; try eassumption.
    done.
  Qed.

  Global Instance basic_equiv_m:
    Proper (lequiv ==> eq ==> equivOP ==> lequiv ==> lequiv) basic.
  Proof. 
    split; apply basic_entails_m. apply H. done. apply H1. apply H2. apply H. done. 
    apply H1. apply H2. 
  Qed.

  (* Annoying extra instances to work around a bug with setoid rewriting on the 
     fourth argument in the general morphism above *)
  Global Instance basic_entails_m' P c:
    Proper (eq ==> lentails ++> lentails) (basic P c).
  Proof.
    repeat move => *. subst; apply: basic_roc; try eassumption. done. reflexivity. done. 
  Qed.

  Global Instance basic_entails_m'' P c O :
    Proper (Basics.flip lentails ++> Basics.flip lentails) (basic P c O).
  Proof.
    move => Q Q' H. apply: basic_roc. done. apply H. reflexivity. done. 
  Qed.

  Global Instance basic_equiv_m' P c:
    Proper (equivOP ==> lequiv ==> lequiv) (basic P c).
  Proof.
    move => O O' HO Q Q' HQ. setoid_rewrite HO. split. by setoid_rewrite HQ. 
    by setoid_rewrite <-HQ. 
  Qed. 

  (* Special case of consequence for precondition *)
  Lemma basic_roc_pre P' S P c O Q:
    P |-- P' ->
    S |-- basic P' c O Q ->
    S |-- basic P c O Q.
  Proof. move=> HP H. by rewrite ->HP. Qed.

  (* Special case of consequence for postcondition *)
  Lemma basic_roc_post Q' S P c O Q:
    Q' |-- Q -> 
    S |-- basic P c O Q' ->
    S |-- basic P c O Q.
  Proof. move=> HQ H. by rewrite <- HQ. Qed. 

  Lemma basic_exists A S P c O Q:
    (forall a:A, S |-- basic (P a) c O Q) ->
    S |-- basic (lexists P) c O Q.
  Proof. rewrite /basic => H. specintros => i j O' a. eforalls H. simple apply H. Qed.

  Global Instance AtEx_basic P c O Q : AtEx (basic P c O Q).
  Proof. rewrite /basic. apply AtEx_forall => i. 
  apply AtEx_forall => j. apply AtEx_forall => O'. apply _. Qed. 

  Lemma basic_basic_context R S' P' O' Q' S P c O Q:
    S' |-- basic P' c O' Q' ->
    S |-- S' ->
    P |-- P' ** R ->
    entailsOP O' O -> 
    Q' ** R |-- Q ->
    S |-- basic P c O Q.
  Proof. move=> Hc HS HP HO HQ. apply: basic_roc. apply HP. apply HQ. apply HO.
  rewrite -> HS. exact: basic_frame. Qed.

  (* Combine rule of consequence and frame *)
  Lemma basic_basic R P' Q' O S P c Q:
    |-- basic P' c O Q' ->
    P |-- P' ** R ->
    Q' ** R |-- Q ->
    S |-- basic P c O Q.
  Proof.
    move=> Hc HP HQ. apply: basic_basic_context; try eassumption. done. done.
  Qed.
End Basic.

Hint Rewrite @spec_at_basic @spec_at_basic : push_at.

Hint Unfold basic : specapply.

Module Export Existentials_basic.
  Import Existentials.

  Lemma pq_basic {M} {HM: MemIs M} t c O Q:
    match find t with
    | Some (mkf _ f) =>
        PullQuant (basic (eval t) c O Q) (fun a => basic (f a) c O Q)
    | None => True
    end.
  Proof.
    move: (@find_correct_pull t). case: (find t) => [[A f]|]; last done.
    red. move=> Heval. rewrite ->Heval.
    apply basic_exists => a. by apply lforallL with a.
  Qed.

  Hint Extern 0 (PullQuant (@basic ?M ?HM ?P ?c ?O ?Q) _) =>
    let t := quote_term P in
    apply (@pq_basic M HM t c O Q) : pullquant.

End Existentials_basic.
