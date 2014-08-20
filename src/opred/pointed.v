(** * Inhabitation (pointedness) of predicates over observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.x86.ioaction.
Require Import x86proved.ilogic_pointed x86proved.opred.core.
Require Export x86proved.pointed. (** We want all the pointed instances *)
Require Coq.Lists.Streams.
Require Import Coq.Classes.RelationClasses.

Generalizable All Variables.
Set Implicit Arguments.

Notation IsPointed_OPred P := (IsPointed (exists x : Actions, ILFunFrm_pred P x)).
Notation point_OPred P := (@point (exists x : Actions, ILFunFrm_pred P x) _).

(* We require predicates on observations to be non-empty i.e. for there to be
   some sequence of actions for which it holds *)
Record PointedOPred := mkPointedOPred {
  OPred_pred :> OPred;
  OPred_inhabited: IsPointed_OPred OPred_pred
}.

Existing Instance OPred_inhabited.

Canonical default_PointedOPred O `{IsPointed_OPred O} : PointedOPred
  := {| OPred_pred := O ; OPred_inhabited := _ |}.

Arguments mkPointedOPred : clear implicits.

Local Transparent ILFun_Ops ILPre_Ops osepILogicOps osepILogic lentails ltrue lfalse limpl land lor lforall lexists eq_opred_stream map_opred_to_stream.

Lemma inhabitedOP (O: PointedOPred) : exists s, O s.
Proof. by destruct O. Qed.

Instance IsPointed_Actions : IsPointed Actions := nil.
Instance IsPointed_eq_opred x : IsPointed_OPred (eq_opred x) := ex_intro _ x (reflexivity _).
Instance IsPointed_empOP : IsPointed_OPred empOP := _.
Instance IsPointed_inOP c d : IsPointed_OPred (inOP c d) := _.
Instance IsPointed_outOP c d : IsPointed_OPred (outOP c d) := _.
Instance IsPointed_catOP `{IsPointed_OPred P, IsPointed_OPred Q} : IsPointed_OPred (catOP P Q).
Proof.
  hnf.
  destruct (point_OPred P), (point_OPred Q).
  eexists (_ ++ _), _, _.
  do !esplit; eassumption.
Qed.
Instance IsPointed_flip_catOP `{IsPointed_OPred P, IsPointed_OPred Q} : IsPointed_OPred (Basics.flip catOP P Q) := IsPointed_catOP.
Instance IsPointed_repOP0 P : IsPointed_OPred (repOP 0 P) | 0 := _.
Instance IsPointed_rollOP0 f : IsPointed_OPred (rollOP 0 f) | 0 := _.
Instance IsPointed_partial_rollOP0 f start : IsPointed_OPred (partial_rollOP f start 0) | 0 := _.
Instance IsPointed_repOP n `{IsPointed_OPred P} : IsPointed_OPred (repOP n P).
Proof.
  induction n; typeclasses eauto.
Qed.
Instance IsPointed_rollOP n f `{forall n, IsPointed_OPred (f (S n))} : IsPointed_OPred (rollOP n f).
Proof.
  induction n; typeclasses eauto.
Qed.
Instance IsPointed_partial_rollOP f count `{forall n, IsPointed_OPred (f n)} : forall start, IsPointed_OPred (partial_rollOP f start count).
Proof.
  induction count; typeclasses eauto.
Qed.

Instance IsPointed_ltrueOP : IsPointed_OPred ltrue := _.
Instance IsPointed_lexistsOP {T P} `{IsPointed T, IsPointed_OPred (P (point T))} : IsPointed_OPred (lexists P).
Proof.
  hnf.
  destruct (point_OPred (P (point T))).
  do 2 esplit; eassumption.
Qed.
Instance IsPointed_lorLOP {P Q} `{IsPointed_OPred P} : IsPointed_OPred (P \\// Q).
Proof.
  hnf.
  destruct (point_OPred P).
  esplit; left; eassumption.
Qed.
Instance IsPointed_lorROP {P Q} `{IsPointed_OPred Q} : IsPointed_OPred (P \\// Q).
Proof.
  hnf.
  destruct (point_OPred Q).
  esplit; right; eassumption.
Qed.
Instance IsPointed_limplOP {P Q} `{IsPointed_OPred Q} : IsPointed_OPred (P -->> Q).
Proof.
  hnf.
  destruct (point_OPred Q).
  esplit.
  setoid_rewrite <- (@limplAdj _ _ _ _ _ ltrue); first by exact I.
  move => ?; eassumption.
Qed.

Instance IsPointed_starOP P : IsPointed_OPred (starOP P) := let _ := 0 : IsPointed nat in IsPointed_lexistsOP.
Instance IsPointed_roll_starOP f start : IsPointed_OPred (roll_starOP f start) := let _ := 0 : IsPointed nat in IsPointed_lexistsOP.

(** Common case *)
Instance IsPointed_lorLempOP {Q} : IsPointed_OPred (empOP \\// Q) := _.
Instance IsPointed_lorRempOP {P} : IsPointed_OPred (P \\// empOP) := _.

Instance IsPointed_foldrOP A B C f g (init : A * B) `{IsPointed_OPred (g init)}
         `{forall a acc, IsPointed_OPred (g acc) -> IsPointed_OPred (g (f a acc))}
         (ls : seq C)
: IsPointed_OPred (g (foldr f init ls)).
Proof.
  induction ls; simpl in *; auto.
Qed.

Instance IsPointed_ifOP b A B `{IsPointed_OPred A, IsPointed_OPred B}
: IsPointed_OPred (if b then A else B).
Proof. by destruct b. Qed.

Instance IsPointedOP_foldr {T} (ls : seq T) f o0 `{IsPointed_OPred o0, forall x y, IsPointed_OPred y -> IsPointed_OPred (f x y)}
: IsPointed_OPred (foldr f o0 ls).
Proof.
  generalize dependent o0.
  induction ls; simpl in *; typeclasses eauto.
Qed.

Instance IsPointedOP_foldl {T} (ls : seq T) f o0 `{IsPointed_OPred o0, forall x y, IsPointed_OPred x -> IsPointed_OPred (f x y)}
: IsPointed_OPred (foldl f o0 ls).
Proof.
  generalize dependent o0.
  induction ls; simpl in *; typeclasses eauto.
Qed.

Instance IsPointed_foldlOP A B C f g (init : A * B) `{IsPointed_OPred (g init)}
         `{forall a acc, IsPointed_OPred (g acc) -> IsPointed_OPred (g (f acc a))}
         (ls : seq C)
: IsPointed_OPred (g (foldl f init ls)).
Proof.
  generalize dependent init.
  induction ls; simpl in *; auto.
Qed.

Fixpoint all_IsPointed_OPred (ls : seq OPred) :=
  if ls is x::xs return Type
  then (IsPointed_OPred x * all_IsPointed_OPred xs)%type
  else unit.
Existing Class all_IsPointed_OPred.

Instance map_all_IsPointed_OPred {T} (ls : seq T) (f : T -> OPred)
         `{forall x, IsPointed_OPred (f x)}
: all_IsPointed_OPred (map f ls).
Proof. induction ls => //=. Qed.

Instance map_map_all_IsPointed_OPred {A B} (ls : seq A) (f : B -> OPred) (g : A -> B)
         `{all_IsPointed_OPred (map (f \o g) ls)}
: all_IsPointed_OPred (map f (map g ls)).
Proof. by rewrite -map_comp. Qed.

Hint Extern 1 => match goal with
                   | [ H : all_IsPointed_OPred _ |- _ ] => destruct H
                 end : typeclass_instances.

Local Opaque catOP IsPointed.

Local Obligation Tactic :=
  intros;
  try match goal with
        | [ |- @ex Actions ?P ] => change (IsPointed (ex P))
      end;
  repeat match goal with
           | [ O : OPred |- _ ] => generalize dependent O
         end;
  try typeclasses eauto;
  try (let ls := match goal with ls : seq _ |- _ => constr:(ls) end in
       induction ls => //=);
  try typeclasses eauto.

Program Instance IsPointed_foldl_map_catOP {T} (ls : seq T) f (o0 : OPred) `{IsPointed_OPred o0, all_IsPointed_OPred (map f ls)}
: IsPointed_OPred (foldl catOP o0 (map f ls)).
Program Instance IsPointed_foldr_map_catOP {T} (ls : seq T) f (o0 : OPred) `{IsPointed_OPred o0, all_IsPointed_OPred (map f ls)}
: IsPointed_OPred (foldr catOP o0 (map f ls)).

Program Instance IsPointed_foldl_map_flip_catOP {T} (ls : seq T) f (o0 : OPred) `{IsPointed_OPred o0, all_IsPointed_OPred (map f ls)}
: IsPointed_OPred (foldl (Basics.flip catOP) o0 (map f ls)).
Program Instance IsPointed_foldr_map_flip_catOP {T} (ls : seq T) f (o0 : OPred) `{IsPointed_OPred o0, all_IsPointed_OPred (map f ls)}
: IsPointed_OPred (foldr (Basics.flip catOP) o0 (map f ls)).

Program Instance IsPointed_foldr_map_fun_catOP {T} (ls : seq T) f g (o0 : OPred)
        `{IsPointed_OPred o0, forall x y, IsPointed_OPred y -> IsPointed_OPred (g x y), all_IsPointed_OPred (map f ls)}
: IsPointed_OPred (foldr (fun (x : T) y => catOP (f x) (g x y)) o0 ls).
Program Instance IsPointed_foldl_map_fun_catOP {T} (ls : seq T) f g (o0 : OPred)
        `{IsPointed_OPred o0, forall x y, IsPointed_OPred y -> IsPointed_OPred (g x y), all_IsPointed_OPred (map f ls)}
: IsPointed_OPred (foldl (fun x (y : T) => catOP (g y x) (f y)) o0 ls).

Program Instance IsPointed_foldr_map_fun_flip_catOP {T} (ls : seq T) f g (o0 : OPred)
        `{IsPointed_OPred o0, forall x y, IsPointed_OPred y -> IsPointed_OPred (g x y), all_IsPointed_OPred (map f ls)}
: IsPointed_OPred (foldr (fun (x : T) y => catOP (g x y) (f x)) o0 ls).
Program Instance IsPointed_foldl_map_fun_flip_catOP {T} (ls : seq T) f g (o0 : OPred)
        `{IsPointed_OPred o0, forall x y, IsPointed_OPred y -> IsPointed_OPred (g x y), all_IsPointed_OPred (map f ls)}
: IsPointed_OPred (foldl (fun x (y : T) => catOP (f y) (g y x)) o0 ls).

(** ** Equality with a prefix of a stream *)
Instance IsPointed_eq_opred_stream (x : Streams.Stream Action) : IsPointed_OPred (eq_opred_stream x) := ex_intro _ nil I.

(** Generate [eq_opred_stream] by mapping and folding *)
Instance IsPointed_map_opred_to_stream {T f1 f2 s} : IsPointed_OPred (@map_opred_to_stream T f1 f2 s) := _.
