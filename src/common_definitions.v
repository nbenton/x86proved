(** * Various useful general purpose notations and definitions *)
Require Import Ssreflect.ssreflect Ssreflect.seq Ssreflect.ssrbool.
Require Import Coq.Lists.Streams.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implcit Arguments.

Notation eta_expand x := (fst x, snd x).

Definition prod_eta A B (p : A * B) : p = eta_expand p
    := match p as p return p = eta_expand p with
         | (x, y) => Coq.Init.Logic.eq_refl
       end.

Fixpoint rep_apply n {A} (f : A -> A) (x : A) : A :=
  match n with
    | 0 => x
    | S n' => f (rep_apply n' f x)
  end.

  Lemma match_match_bool_option b T T' oT oF s n
: match match b return option T with
          | true => oT
          | false => oF
        end as o return T' o with
    | Some x => s x
    | None => n
  end
  = match b as b return T' (match b return option T with
                              | true => oT
                              | false => oF
                            end) with
      | true => match oT with
                  | Some x => s x
                  | None => n
                end
      | false => match oF with
                   | Some x => s x
                   | None => n
                 end
    end.
Proof. destruct b, oT, oF; reflexivity. Defined.
Lemma match_match_bool_pair b A B T xT xF P
: match match b return prod A B with
          | true => xT
          | false => xF
        end as p return T p with
    | (x, y) => P x y
  end
  = match b as b return T (match b as b return prod A B with
                             | true => xT
                             | false => xF
                           end) with
      | true => match xT with
                  | (x, y) => P x y
                end
      | false => match xF with
                   | (x, y) => P x y
                 end
    end.
Proof. destruct b, xT, xF; reflexivity. Defined.
Lemma match_pair_eta A B (p : prod A B) T P
: match p return T with
    | (x, y) => P x y
  end
  = P (fst p) (snd p).
Proof. destruct p; reflexivity. Defined.
Lemma match_bool_fn b A B xT xF
: match b as b return forall x : A, B b x with
    | true => xT
    | false => xF
  end
  = fun x : A => match b as b return B b x with
                   | true => xT x
                   | false => xF x
                 end.
Proof. destruct b; reflexivity. Defined.
Lemma match_option_const T (b : option T) A x
: match b as b return A with
    | Some _ => x
    | None => x
  end
  = x.
Proof. destruct b; reflexivity. Defined.
Lemma match_option_fn T (b : option T) A B s n
: match b as b return forall x : A, B b x with
    | Some k => s k
    | None => n
  end
  = fun x : A => match b as b return B b x with
                   | Some k => s k x
                   | None => n x
                 end.
Proof. destruct b; reflexivity. Defined.
Lemma match_option_match_pair_eta A B (p : option (prod A B)) T Ps Pn
: match p return T with
    | Some k => match k return T with
                  | (x, y) => Ps x y
                end
    | None => Pn
  end
  = match p return T with
      | Some k => Ps (fst k) (snd k)
      | None => Pn
    end.
Proof. destruct p as [[? ?]|]; reflexivity. Defined.
Lemma match_option_match_pair_eta_fun A B (p : option (prod A B)) T T' a Ps Pn
: match p return T' with
    | Some k => match k as k return T k -> T' with
                  | (x, y) => Ps x y
                end (a k)
    | None => Pn
  end
  = match p return T' with
      | Some k => Ps (fst k) (snd k) (a (fst k, snd k))
      | None => Pn
    end.
Proof. destruct p as [[? ?]|]; reflexivity. Defined.
Lemma match_option_comm_1 T (p : option T) A B (f : forall x : A, B x) s n
: match p as p return B match p with
                          | Some k => s k
                          | None => n
                        end with
    | Some k => f (s k)
    | None => f n
  end
  = f match p return A with
        | Some k => s k
        | None => n
      end.
Proof. destruct p; reflexivity. Defined.
Lemma match_option_comm_2 T (p : option T) A B R (f : forall (x : A) (y : B x), R x y) (s1 : T -> A) (s2 : forall x : T, B (s1 x)) n1 n2
: match p as p return R match p with
                          | Some k => s1 k
                          | None => n1
                        end
                        match p as p return B match p with Some k => s1 k | None => n1 end with
                          | Some k => s2 k
                          | None => n2
                        end with
    | Some k => f (s1 k) (s2 k)
    | None => f n1 n2
  end
  = f match p return A with
        | Some k => s1 k
        | None => n1
      end
      match p as p return B match p with Some k => s1 k | None => n1 end with
        | Some k => s2 k
        | None => n2
      end.
Proof. destruct p; reflexivity. Defined.
Definition match_option_comm_1_const T (p : option T) A B (f : A -> B) s n
: (match p return B with
     | Some k => f (s k)
     | None => f n
   end)
  = (f match p return A with
         | Some k => s k
         | None => n
       end)
  := @match_option_comm_1 T p A _ f s n.
Definition match_option_comm_2_const T (p : option T) A B R (f : A -> B -> R) s1 s2 n1 n2
: (match p return R with
     | Some k => f (s1 k) (s2 k)
     | None => f n1 n2
   end)
  = (f match p return A with
         | Some k => s1 k
         | None => n1
       end
       match p return B with
         | Some k => s2 k
         | None => n2
       end)
  := @match_option_comm_2 T p A _ _ f s1 s2 n1 n2.
Lemma match_bool_comm_1 (b : bool) A B (F : forall x : A, B x) t f
: (if b as b return B (if b then t else f) then F t else F f)
  = F (if b then t else f).
Proof. destruct b; reflexivity. Defined.
Lemma match_bool_comm_2 (b : bool) A B R (F : forall (x : A) (y : B x), R x y) t1 f1 t2 f2
: (if b as b return R (if b then t1 else f1) (if b as b return B (if b then t1 else f1) then t2 else f2) then F t1 t2 else F f1 f2)
  = F (if b then t1 else f1) (if b as b return B (if b then t1 else f1) then t2 else f2).
Proof. destruct b; reflexivity. Defined.
Definition match_bool_comm_1_const (b : bool) A R (F : A -> R) t f
: (if b then F t else F f) = F (if b then t else f)
  := @match_bool_comm_1 b _ _ F t f.
Definition match_bool_comm_2_const (b : bool) A B R (F : A -> B -> R) t1 f1 t2 f2
: (if b then F t1 t2 else F f1 f2) = F (if b then t1 else f1) (if b then t2 else f2)
  := @match_bool_comm_2 b _ _ _ F t1 f1 t2 f2.
Lemma match_bool_const (b : bool) A x : (if b return A then x else x) = x.
Proof. destruct b; reflexivity. Defined.
Lemma if_else_False_iff b P : (if b then P else False) <-> (P /\ (b = true)).
Proof. destruct b; intuition. Qed.

Hint Rewrite match_option_const match_match_bool_option match_match_bool_pair match_pair_eta match_bool_fn match_option_fn match_option_match_pair_eta match_option_match_pair_eta_fun match_option_comm_1 match_option_comm_2 match_option_comm_1_const match_option_comm_2_const match_bool_comm_1 match_bool_comm_2 match_bool_comm_1_const match_bool_comm_2_const match_bool_const if_else_False_iff : matchdb.

Ltac ssr_autorewrite_with_matchdb' :=
  (** Order matters; do the things involving only one [match] first, and then do the things involving multiple matches. *)
  do [ rewrite match_bool_fn
     | rewrite match_option_fn
     | rewrite match_bool_const
     | rewrite match_option_const
     | rewrite if_else_False_iff
     | rewrite match_pair_eta
     | rewrite match_option_match_pair_eta
     | rewrite match_option_match_pair_eta_fun
     | rewrite match_match_bool_option
     | rewrite match_match_bool_pair
     | rewrite match_option_comm_1
     | rewrite match_option_comm_2
     | rewrite match_option_comm_1_const
     | rewrite match_option_comm_2_const
     | rewrite match_bool_comm_1
     | rewrite match_bool_comm_2
     | rewrite match_bool_comm_1_const
     | rewrite match_bool_comm_2_const ].

Ltac ssr_autorewrite_with_matchdb := do !ssr_autorewrite_with_matchdb'.

Definition paths_prod A B (x y : A * B) (H : x = y) : fst x = fst y /\ snd x = snd y
  := conj (f_equal (@fst _ _) H) (f_equal (@snd _ _) H).

Definition paths_option T (x y : option T) (H : x = y) : match x, y with
                                                           | Some x', Some y' => x' = y'
                                                           | None, None => True
                                                           | _, _ => False
                                                         end.
Proof.
  destruct H, x; constructor.
Defined.

Definition specialize_forall {A B C} (H : forall x : A, B x -> C x) : (forall x : A, B x) -> (forall x : A, C x)
  := fun f x => H x (f x).
Definition specialize_ex {A} {B C : A -> Prop} (H : forall x, B x -> C x) : (exists x : A, B x) -> (exists x : A, C x)
  := fun x => match x with
                | ex_intro x fx => ex_intro _ x (H x fx)
              end.

(** Extensionality of [forall]s follows from functional extensionality. *)
Lemma forall_extensionality {A} {B C : A -> Type} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof.
  apply functional_extensionality in H. destruct H. reflexivity.
Defined.

Lemma forall_extensionalityP {A} {B C : A -> Prop} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof.
  apply functional_extensionality in H. destruct H. reflexivity.
Defined.

Lemma forall_extensionalityS {A} {B C : A -> Set} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof.
  apply functional_extensionality in H. destruct H. reflexivity.
Defined.

Lemma bool_neq_negb (a b : bool) : (a <> b) <-> (a = negb b).
Proof.
  destruct a, b; split; simpl; congruence.
Qed.

Lemma all_behead {T} (xs : seq T) P : all P xs -> all P (behead xs).
Proof.
  destruct xs as [|x xs] => //=.
  by destruct (P x).
Qed.

(** Checks that the last element satisfies the predicate, and the rest do not. *)
Fixpoint only_last {T} (P : pred T) (x : T) (xs : seq T) : bool
  := match xs with
       | nil => P x
       | x'::xs' => ~~P x && only_last P x' xs'
     end.

Lemma only_last_behead {T} (P : pred T) x xs
: only_last P x xs -> only_last P (head x xs) (behead xs).
Proof.
  revert x.
  induction xs => //= x.
  destruct (P x) => //=.
Qed.

Fixpoint drop_last {T} (x : T) (xs : seq T) :=
  match xs with
    | nil => nil
    | x'::xs' => x::drop_last x' xs'
  end.

Definition only_last' {T} (P : pred T) (x : T) (xs : seq T) : bool
  := all (fun x => ~~P x) (drop_last x xs) && P (last x xs).

Arguments only_last' / .

Lemma only_last__only_last' {T} P x xs : @only_last T P x xs = @only_last' T P x xs.
Proof.
  move: x.
  induction xs => //=.
  move => x.
  destruct (P x) => //=.
  rewrite IHxs => //=.
Qed.

Fixpoint list_is_prefix_of_stream {T} (s : Stream T) (ls : seq T) : Prop :=
  match ls with
    | nil => True
    | x::xs => match s with
                 | Cons x' xs' => x = x' /\ list_is_prefix_of_stream xs' xs
               end
  end.

Fixpoint stream_prepend_list {T} (ls : seq T) (rest : Stream T) : Stream T :=
  match ls with
    | nil => rest
    | x::xs => Cons x (stream_prepend_list xs rest)
  end.

CoFixpoint flatten_stream {T} (s : Stream (T * seq T)) : Stream T :=
  match s with
    | Cons x xs => Cons (fst x) (flatten_stream (if snd x is x'::xs' then Cons (x', xs') xs else xs))
  end.

Lemma snd_foldl {A B C} accA accB initA initB xs
: snd (foldl (fun (xy : A * B) (v : C) => (accA (fst xy) v, accB (snd xy) v)) (initA, initB) xs)
  = foldl accB initB xs.
Proof.
  revert initA initB.
  induction xs => //= *.
Qed.
