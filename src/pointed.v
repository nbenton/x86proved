(** * Pointed types *)
(** A pointed type is a type [T] together with an inhabitant of [T].
    The "pointed" terminology comes from the homotopy type theoretic
    practice of thinking of types as ∞-groupoids or topological
    spaces. *)
Require Import Ssreflect.ssreflect.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses.

Set Implicit Arguments.
Generalizable All Variables.

Class IsPointed (T : Type) := point : T.
Arguments point T {_}.

Instance IsPointed_True : IsPointed True := I.
Instance IsPointed_unit : IsPointed unit := tt.
Instance IsPointed_prod `{IsPointed A, IsPointed B} : IsPointed (A * B) := (point A, point B).
Instance IsPointed_and {A B : Prop} `{IsPointed A, IsPointed B} : IsPointed (A /\ B) := conj (point A) (point B).
Instance IsPointed_sigT `{IsPointed A, IsPointed (P (point A))} : IsPointed (sigT P) := existT P _ (point (P (point A))).
Instance IsPointed_sig {A} {P : A -> Prop} `{IsPointed A, IsPointed (P (point A))} : IsPointed (sig P) := exist P _ (point (P (point A))).
Instance IsPointed_ex {A} {P : A -> Prop} `{IsPointed A, IsPointed (P (point A))} : IsPointed (ex P) := ex_intro P _ (point (P (point A))).
Instance IsPointed_sigT2 `{IsPointed A, IsPointed (P (point A)), IsPointed (Q (point A))} : IsPointed (sigT2 P Q)
  := existT2 P Q (point A) (point _) (point _).
Instance IsPointed_sig2 {A} {P Q : A -> Prop} `{IsPointed A, IsPointed (P (point A)), IsPointed (Q (point A))} : IsPointed (sig2 P Q)
  := exist2 P Q (point A) (point _) (point _).
Instance IsPointed_ex2 {A} {P Q : A -> Prop} `{IsPointed A, IsPointed (P (point A)), IsPointed (Q (point A))} : IsPointed (ex2 P Q)
  := ex_intro2 P Q (point A) (point _) (point _).
Instance IsPointed_forall {A B} `{forall a : A, IsPointed (B a)} : IsPointed (forall a : A, B a) := fun a => point (B a).
Instance IsPointed_refl {T a} : IsPointed (a = a :> T) := eq_refl.
Instance IsPointed_reflexive `{@Reflexive T R} {a} : IsPointed (R a a) := reflexivity _.

(** TODO(t-jagro): Should this be an instance? *)
Instance IsPointed_list {A} : IsPointed (list A) := nil.
Instance IsPointed_nat : IsPointed nat := 0.

(** We don't make the [or] versions instances, because they're not unique *)
Definition IsPointed_sum_inl {A B} `{IsPointed A} : IsPointed (A + B) := inl (point A).
Definition IsPointed_sum_inr {A B} `{IsPointed B} : IsPointed (A + B) := inr (point B).
Definition IsPointed_or_introl {A B : Prop} `{IsPointed A} : IsPointed (A \/ B) := or_introl (point A).
Definition IsPointed_or_intror {A B : Prop} `{IsPointed B} : IsPointed (A \/ B) := or_intror (point B).
