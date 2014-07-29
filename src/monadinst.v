(*===========================================================================
    Some useful instances of Monad
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.finfun Ssreflect.fintype.
Require Import x86proved.monad.
Require Import Coq.Lists.Streams.
Require Import x86proved.common_tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.FunctionalExtensionality.

(*---------------------------------------------------------------------------
    Option monad
  ---------------------------------------------------------------------------*)
Instance optionMonadOps : MonadOps option :=
{ retn := Some
; bind := fun X Y (c: option X) f => if c is Some y then f y else None }.

Instance optionMonad : Monad option.
Proof. apply Build_Monad. done. move => X; by case. move => X Y Z; by case. Qed.

(*---------------------------------------------------------------------------
    Error monad
  ---------------------------------------------------------------------------*)
Section Error.

  Variable F: Type.

  Inductive Result X :=
  | Error (f:F)
  | Success (x:X).

  Global Instance errorMonadOps : MonadOps Result :=
  { retn := Success
  ; bind := fun X Y (c: Result X) f =>
    match c with Success x => f x | Error e => Error _ e end }.

  Global Instance errorMonad : Monad Result.
  Proof. apply Build_Monad. done. move => X; by case. move => X Y Z; by case. Qed.

  Definition raiseError {X} e : Result X := Error _ e.

End Error.

(*---------------------------------------------------------------------------
    List monad
    @todo akenn: fix this so we don't get a universe inconsistency later!
  ---------------------------------------------------------------------------*)
(*
Lemma flatten_map_cat {A B} (f:A->seq B) x y :
  flatten (map f (x ++ y)) = flatten (map f x) ++ flatten (map f y).
Proof. induction x => //. by rewrite /= IHx catA. Qed.

Instance seqMonadOps : MonadOps seq :=
{ retn := fun X (x:X) => x::nil
; bind := fun X Y (x: seq X) f => flatten (map f x) }.

Instance seqMonad : Monad seq.
Proof. apply Build_Monad.
+ move => X Y x f. by rewrite /= cats0.
+ move => X c. rewrite /=. induction c => //. by rewrite /=IHc.
+ induction c => //. move => f g. rewrite/=flatten_map_cat. rewrite/= in IHc. by rewrite IHc.
Qed.
*)
(*---------------------------------------------------------------------------
    I/O monad. D is the type of the input/output data
  ---------------------------------------------------------------------------*)
Section IO.

  Variable Chan: Type.
  Variable D: Type.

  Inductive IOM X :=
  | retnIO (x:X)
  | Out (ch:Chan) (d:D) (rest:IOM X)
  | In (ch:Chan) (f:D -> IOM X).

  Fixpoint bindIO X Y (c: IOM X) (f: X -> IOM Y) :=
   match c with
   | retnIO y => f y
   | Out ch d rest => Out ch d (bindIO rest f)
   | In ch g => In ch (fun d => bindIO (g d) f)
   end.

  Global Instance IOMonadOps : MonadOps IOM :=
  { retn := retnIO; bind := bindIO }.

  Global Instance IOMonad : Monad IOM.
  Proof. apply Build_Monad.
  (* assoc *) done.
  (* id_l *) induction c => //.
  + rewrite /= in IHc. by rewrite /=IHc.
  + rewrite /=. rewrite /= in H. by rewrite (functional_extensionality _ _ H).
  (* id_r *) induction c => //.
  + move => f g. rewrite /= in IHc. by rewrite /=IHc.
  + move => f0 g. rewrite /= in H.
    rewrite /=. apply f_equal. apply functional_extensionality. move => d. by rewrite H.
  Qed.

  Definition IO_write ch d : IOM unit := Out ch d (retn tt).
  Definition IO_read ch : IOM D := In ch retn.

  Section IO_run.
    Hypothesis Chan_eq : @Equality.mixin_of Chan.

    Let chan_eqType := Eval hnf in EqType _ Chan_eq.

    Fixpoint IO_run X (s:Chan -> Stream D) (m: IOM X) : (Chan -> Stream D) * (seq (Chan * D) * X) :=
      match m with
        | retnIO x => (s, (nil,x))
        | In ch g => IO_run (fun ch' : chan_eqType => if ch' == ch then tl (s ch') else s ch') (g (hd (s ch)))
        | Out ch d m => let s' := fst (IO_run s m) in
                        let output := fst (snd (IO_run s m)) in
                        let result := snd (snd (IO_run s m)) in
                        (s', (cons (ch, d) output, result))
      end.

    Definition IO_run_output X s m : seq (Chan * D) * X := snd (@IO_run X s m).

    Lemma IO_run_output_commute_if X s b m1 m2
    : @IO_run_output X s (if b then m1 else m2) = if b then (@IO_run_output X s m1) else (@IO_run_output X s m2).
    Proof. by destruct b. Defined.

    Lemma IO_run_output_commute_option X Y s (b : option Y) m1 m2
    : @IO_run_output X s (match b with Some k => m1 k | None => m2 end) = match b with Some k => @IO_run_output X s (m1 k) | None => @IO_run_output X s m2 end.
    Proof. by destruct b. Defined.

    Lemma IO_run_bindIO_eq X Y inputs1 (m1: IOM X) (m2 : X -> IOM Y)
          (inputs2 := fst (IO_run inputs1 m1))
          (out1 := fst (snd (IO_run inputs1 m1)))
          (x1 := snd (snd (IO_run inputs1 m1)))
          (inputs := fst (IO_run inputs2 (m2 x1)))
          (out2 := fst (snd (IO_run inputs2 (m2 x1))))
          (x2 := snd (snd (IO_run inputs2 (m2 x1))))
    : @IO_run Y inputs1 (bindIO m1 m2) = (inputs, (out1 ++ out2, x2)).
    Proof.
      revert m2 inputs1 x1 inputs2 inputs x2 out1 out2.
      induction m1; try by simpl; intros; simpl_paths; simpl in *; subst.
      { simpl; intros; erewrite IHm1;
        do !(idtac;
             match goal with
               | _ => progress subst
               | _ => progress simpl in *
               | _ => evar_safe_reflexivity
               | [ |- ?a :: ?b ++ ?c = ?a :: ?b' ++ ?c' ] => (apply f_equal; reflexivity)
               | _ => progress simpl_paths
             end). }
      { intros; hyp_eapply *. }
    Qed.

    Lemma IO_run_bindIO X Y inputs1 inputs2 inputs (m1: IOM X) m2 out1 out2 out x1 x2
          (H1 : IO_run inputs1 m1 = (inputs2, (out1, x1)))
          (H2 : IO_run inputs2 (m2 x1) = (inputs, (out2, x2)))
          (H3 : out1 ++ out2 = out)
    : @IO_run Y inputs1 (bindIO m1 m2) = (inputs, (out, x2)).
    Proof.
      rewrite IO_run_bindIO_eq.
        by do !hyp_rewrite *.
    Qed.

    Lemma IO_run_output_bindIO_eq X Y inputs1 (m1: IOM X) m2
          (inputs2 := fst (IO_run inputs1 m1))
          (out1 := fst (snd (IO_run inputs1 m1)))
          (x1 := snd (snd (IO_run inputs1 m1)))
          (inputs := fst (IO_run inputs2 (m2 x1)))
          (out2 := fst (IO_run_output inputs2 (m2 x1)))
          (x2 := snd (IO_run_output inputs2 (m2 x1)))
    : @IO_run_output Y inputs1 (bindIO m1 m2) = (out1 ++ out2, x2).
    Proof.
      unfold IO_run_output in *.
      rewrite IO_run_bindIO_eq.
      simpl; f_equal.
    Qed.

    Lemma IO_run_output_bindIO_helper X Y inputs (m1: IOM X) m2 x2 out
    : (exists inputs' out1 out2 x1,
         out1 ++ out2 = out
         /\ IO_run inputs m1 = (inputs', (out1, x1))
         /\ IO_run_output inputs' (m2 x1) = (out2, x2))
      <-> (@IO_run_output Y inputs (bindIO m1 m2) = (out, x2)).
    Proof.
      rewrite IO_run_output_bindIO_eq; simpl.
      do ![ split
          | move => ?
          | progress destruct_head_hnf ex
          | progress destruct_head_hnf and
          | progress subst
          | progress simpl_paths; simpl in *
          | progress f_equal
          | esplit ].
    Qed.

    Lemma IO_run_output_bindIO_helper' X Y inputs (m1: IOM X) m2 x2 out
    : (let inputs' := fst (IO_run inputs m1) in
       let out1 := fst (snd (IO_run inputs m1)) in
       let x1 := snd (snd (IO_run inputs m1)) in
       let out2 := fst (IO_run_output inputs' (m2 x1)) in
       out1 ++ out2 = out
       /\ snd (IO_run_output inputs' (m2 x1)) = x2)
      <-> (@IO_run_output Y inputs (bindIO m1 m2) = (out, x2)).
    Proof.
      etransitivity; [ | by apply IO_run_output_bindIO_helper ].
      do ![ split
          | progress simpl
          | move => ?
          | progress subst
          | progress destruct_head_hnf ex
          | progress destruct_head_hnf prod
          | progress destruct_head_hnf and
          | by do ?esplit; try simpl_paths; simpl in *; subst; simpl ].
    Qed.
  End IO_run.

  Definition OutputM X := (seq D * X)%type.

  Global Instance OutputMonadOps : MonadOps OutputM :=
  { retn := fun {X} (x:X) => (nil, x);
    bind := fun {X Y} (c: OutputM X) (f: X -> OutputM Y) =>
            let (s, x) := c in
            let (s', y) := f x in (s++s', y) }.

  Global Instance OutputMonad : Monad OutputM.
  Proof. apply Build_Monad.
  (* assoc *) move => X Y x f. rewrite /bind/retn/=. by case (f x).
  (* id_l *) move => X c. rewrite /bind/retn/=. case c => s x. by rewrite cats0.
  (* id_r *) move => X Y Z c f g. case c => s x.
    rewrite /bind/=. case (f x) => s' y. case (g y) => s'' z. by rewrite catA.
  Qed.

  Definition Output_write d : OutputM unit := ([::d], tt).
End IO.

Existing Instance IOMonadOps.
Existing Instance IOMonad.
Existing Instance OutputMonadOps.
Existing Instance OutputMonad.

(*---------------------------------------------------------------------------
    State monad. S is the type of states
  ---------------------------------------------------------------------------*)
Section State.

  Context {S: Type}.

  Definition SM X := S -> (S * X)%type.

  (* Of course, this is a monad *)
  Global Instance SMonadOps : MonadOps SM :=
  { retn := fun X (x: X) (s:S) => (s, x)
  ; bind := fun X Y (c: SM X) (f: X -> SM Y) =>
            fun s => let (st1, a1) := c s in f a1 st1 }.

  Global Instance SMonad : Monad SM.
  Proof.
  apply Build_Monad.
  (* assoc *) move => X Y x f. by apply functional_extensionality => s.
  (* id_l *) move => X c. apply functional_extensionality => s. simpl. by elim (c s).
  (* id_r *) move => X Y Z c f g. apply functional_extensionality => s. simpl. by elim (c s).
  Qed.

  Definition SM_get : SM S := fun s => (s,s).
  Definition SM_set (s':S) : SM unit := fun s => (s',tt).

  Lemma bindGet {Y} (s: S) (f: S -> SM Y):
    bind SM_get f s = f s s.
  Proof. done. Qed.

End State.

(*---------------------------------------------------------------------------
    Stateful I/O. S is the type of states, D the type of input/output data
  ---------------------------------------------------------------------------*)
(*
Require Import Streams.
Section StateIO.

  Variable S: Type.
  Variable D: Type.

  Inductive Act := In (d:D) | Out (d:D).

  Definition SO X := S -> seq Act -> S -> X -> Prop.
  Inductive SOtrans X : SO X :=
  | unitSO (x: X) : forall s, SOtrans s nil s x
  | bindSO Y (c: SO Y) (f: Y -> SO X) :
    forall s s' s'' t t' x y, c s t s' y -> f y s' t' s'' x -> SOtrans s (t++t') s'' x.


Check unitSO. SOtrans.
Check unitSO.
  (* Of course, this is a monad *)
  Global Instance SOMonadOps : MonadOps SO :=
  { retn := unitSO
  ; bind := bindSO }. fun X Y (c: SO X) (f: X -> SO Y) =>
            fun str s => let: (st1, xs1, a1) := c str s in
                     let: (st2, xs2, a2) := f a1 str st1 in
                     (st2, xs1++xs2, a2) }.

  Global Instance SOMonad : Monad SO.
  Proof.
  apply Build_Monad.
  (* assoc *) move => X Y x f. apply functional_extensionality => s.
              simpl. by case E: (f x s) => [[st2 xs2] a2].
  (* id_l *) move => X c. apply functional_extensionality => s.
             simpl. case E: c => [[st xs] a]. by rewrite cats0.
  (* id_r *) move => X Y Z c f g. apply functional_extensionality => s.
             simpl. case E1: (c s) => [[st1 xs1] a1].
                    case E2: (f a1 st1) => [[st2 xs2] a2].
                    case E3: (g a2 st2) => [[st3 xs3] a3]. by rewrite catA.
  Qed.

  Definition SO_get : SO S := fun s => (s,nil,s).
  Definition SO_set (s':S) : SO unit := fun s => (s',nil,tt).
  Definition SO_output (d:D) : SO unit := fun s => (s,d::nil,tt).
End StateO.
*)

(*===========================================================================
    Monad transformers
  ===========================================================================*)

Section MonadTransformers.

(* Base monad *)
Variable M: Type -> Type.
Variable ops: MonadOps M.
Variable laws: Monad M.

(*---------------------------------------------------------------------------
    Option monad transformer
  ---------------------------------------------------------------------------*)
(* Base monad *)
Section OptionMT.

  Definition optionMT X := M (option X).

  Global Instance optionMT_ops : MonadOps optionMT :=
  { retn := fun X (x:X) => retn (Some x)
  ; bind := fun X Y (c: optionMT X) (f: X -> optionMT Y) =>
      bind (MonadOps:=ops) c (fun x:option X => if x is Some x' then f x' else retn None) }.

  Global Instance optionMT_laws : Monad optionMT.
  Proof. apply Build_Monad.
  (* assoc *) move => X Y x f. by rewrite /=id_l.
  (* id_l *)  move => X c. rewrite /= -{2}(id_r (option X) c).
    apply: f_equal. apply functional_extensionality => x. by elim x.
  (* id_r *) move => X Y Z c f g. rewrite /=assoc. apply: f_equal.
    apply functional_extensionality => x. elim x => //. by rewrite id_l.
  Qed.

  Global Coercion OMT_lift {X} (c: M X) : optionMT X :=
  let! x = c; retn (Some x).
End OptionMT.

(*---------------------------------------------------------------------------
    Error monad transformer
  ---------------------------------------------------------------------------*)
Section ErrorMT.

  Variable F: Type.

  Definition errorMT X := M (Result F X).

  Global Instance errorMT_ops : MonadOps errorMT :=
  { retn := fun X (x:X) => retn (Success _ x)
  ; bind := fun X Y (c: errorMT X) (f: X -> errorMT Y) =>
            bind (MonadOps:=ops) c (fun x =>
            match x with Success x => f x | Error e => retn (Error _ e) end) }.

  Global Instance errorMT_laws : Monad errorMT.
  Proof. apply Build_Monad.
  (* assoc *) move => X Y x f. by rewrite/= id_l.
  (* id_l *)  move => X c. simpl. rewrite -{2}(id_r (Result _ _) c).
  apply f_equal. apply functional_extensionality => x. by elim x.
  (* id_r *) move => X Y Z c f g. simpl. rewrite assoc.
  apply f_equal. apply functional_extensionality => x.
  elim x => //. move => f'. by rewrite id_l.
  Qed.

  Definition EMT_raise {X} e : errorMT X :=
    retn (Error _ e).

  Definition EMT_trybind {X Y} (c: errorMT X) (f: F -> errorMT Y) (g: X -> errorMT Y):=
    bind (MonadOps := ops) c (fun x =>
    match x with Success x => g x | Error e => f e end).

  Definition EMT_handle {X} (c: errorMT X) (f: F -> errorMT X) : errorMT X :=
    EMT_trybind c f retn.

  Lemma EMT_bind_as_trybind {X Y} (c: errorMT X) (f: X -> errorMT Y) :
    bind c f = EMT_trybind c EMT_raise f.
  Proof. done. Qed.

  Lemma EMT_trybind_retn {X Y} (x:X) (f: F -> errorMT Y) g:
    EMT_trybind (retn x) f g = g x.
  Proof. rewrite /EMT_trybind/=. by rewrite id_l. Qed.

  Global Coercion EMT_lift {X} (c: M X) : errorMT X :=
    let! x = c; retn (Success _ x).

  Lemma EMT_trybind_bind_lift {X Y Z} (c:M X) (f: X -> errorMT Y) (g: F -> errorMT Z) (h: Y -> errorMT Z):
    EMT_trybind (bind c f) g h = bind c (fun x => EMT_trybind (f x) g h).
  Proof. by rewrite /=/EMT_trybind assoc. Qed.

  Lemma EMT_trybind_raise {X Y} e (f: F -> errorMT Y) (g: X -> errorMT Y):
    EMT_trybind (EMT_raise e) f g = f e.
  Proof. rewrite /EMT_trybind/=. rewrite /EMT_raise. by rewrite id_l. Qed.

  Lemma EMT_handle_retn {X} f (x:X):
    EMT_handle (retn x) f = retn x.
  Proof. apply EMT_trybind_retn. Qed.

  Lemma EMT_handle_raise {X} e (f: F -> errorMT X) :
    EMT_handle (EMT_raise e) f = f e.
  Proof. by apply EMT_trybind_raise. Qed.

  Lemma EMT_trybind_lift {X Y} (x:M X) (f: F -> errorMT Y) g:
    EMT_trybind (EMT_lift x) f g = bind x g.
  Proof. rewrite /EMT_trybind/=. rewrite assoc. apply f_equal.
  apply functional_extensionality => y. by rewrite id_l. Qed.

  Lemma EMT_bind_lift {X Y} (x: M X) (f: X -> errorMT Y) :
    bind (EMT_lift x) f = bind x f.
  Proof. apply EMT_trybind_lift. Qed.


End ErrorMT.

(*---------------------------------------------------------------------------
    State monad transformer. S is the type of states, M is underlying monad

    This causes a universe inconsistency with procstatemonad.v!
  ---------------------------------------------------------------------------*)
Section StateMT.

  Variable S: Type.

  Definition SMT X := S -> M (S * X)%type.

  (* Of course, this is a monad *)
  Global Instance SMT_ops : MonadOps SMT :=
  { retn := fun X (x: X) (s:S) => retn (s, x)
  ; bind := fun X Y (c: SMT X) (f: X -> SMT Y) =>
            fun s => let! (st1, a1) = c s; f a1 st1 }.

  Global Instance SMT_laws : Monad SMT.
  Proof.
  assert (H1:forall Z, (fun z:S*Z => let (st,x) := z in retn (T:=M)(st, x)) = fun z => retn z).
  move => Z. apply functional_extensionality. by elim.

  assert(H2: forall Z, (fun z:S*Z => retn z) = retn).
  move => Z. by apply functional_extensionality.

  apply Build_Monad.
  (* assoc *) move => X Y x f. apply functional_extensionality => s. by rewrite /=id_l.
  (* id_l *) move => X c. apply functional_extensionality => s. by rewrite /= H1/= id_r.
  (* id_r *) move => X Y Z c f g. apply functional_extensionality => s.
  rewrite /= assoc/=. apply f_equal. apply functional_extensionality. by elim.
  Qed.

  Definition SMT_get : SMT S := fun s => retn (s,s).
  Definition SMT_set (s':S) : SMT unit := fun s => retn (s',tt).

  Global Coercion SMT_lift {X} (c: M X) : SMT X :=
  fun s => let! r = c; retn (s,r).

  Lemma SMT_bindGet {Y} (s: S) (f: S -> SMT Y):
    bind SMT_get f s = f s s.
  Proof. by rewrite /bind/SMT_get/= id_l. Qed.

  Lemma SMT_doSet {Y} (s s': S) (c: SMT Y):
    (do! SMT_set s'; c) s = c s'.
  Proof. by rewrite /bind/SMT_set/= id_l. Qed.

End StateMT.

End MonadTransformers.

Lemma match_match_bool_result F X (b : bool) xT xF T xE xS
: (match (if b return Result F X then xT else xF) as r return T r with
     | Error f => xE f
     | Success x => xS x
   end)
  = if b as b return T (if b return Result F X then xT else xF)
    then match xT with
           | Error f => xE f
           | Success x => xS x
         end
    else match xF with
           | Error f => xE f
           | Success x => xS x
         end.
Proof. destruct b, xT, xF; reflexivity. Defined.
Hint Rewrite match_match_bool_result : matchdb.

Lemma IO_run_output_commute_if_rewrite Chan D Chan_eq A F X s b m1 m2 T xE xS
: match snd (snd (@IO_run_output Chan D Chan_eq (A * Result F X) s (if b then m1 else m2))) as r return T r with
    | Error f => xE f
    | Success x => xS x
  end = if b as b return T (snd (snd (@IO_run_output Chan D Chan_eq (A * Result F X) s (if b then m1 else m2))))
        then match snd (snd (IO_run_output _ s m1)) as r return T r with
               | Error f => xE f
               | Success x => xS x
             end
        else match snd (snd (IO_run_output _ s m2)) as r return T r with
               | Error f => xE f
               | Success x => xS x
             end.
Proof. by destruct b. Defined.
Hint Rewrite IO_run_output_commute_if_rewrite : matchdb.

Lemma IO_run_output_commute_match_option_rewrite Chan D Chan_eq A F X s T xE xS U (o : option U) Sv Nv
: match snd (snd (@IO_run_output Chan D Chan_eq (A * Result F X) s (match o with Some k => Sv k | None => Nv end))) as r return T r with
    | Error f => xE f
    | Success x => xS x
  end = match o as o return T (snd (snd (@IO_run_output Chan D Chan_eq (A * Result F X) s (match o with Some k => Sv k | None => Nv end)))) with
          | Some k => match snd (snd (snd (IO_run _ s (Sv k)))) as r return T r with
                        | Error f => xE f
                        | Success x => xS x
                      end
          | None => match snd (snd (snd (IO_run _ s Nv))) as r return T r with
                      | Error f => xE f
                      | Success x => xS x
                    end
        end.
Proof. by destruct o. Defined.
Hint Rewrite IO_run_output_commute_match_option_rewrite : matchdb.
