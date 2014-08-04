(** * Various useful general purpose tactics *)
(** Require [ssreflect] so notations like [_ : _] don't break. *)
(** SSReflect breaks [type of].  It also overrides [rewrite], but we
    can get that back via [rewrite -> ] and [rewrite <- ]. *)
Ltac type_of x := type of x.

Require Import Ssreflect.ssreflect Ssreflect.seq.
Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export x86proved.common_definitions.

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail tac "succeeds"; [](* test for [t] solved all goals *)).

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").

(** fail if [x] is a function application, a dependent product ([fun _
    => _]), or a pi type ([forall _, _]), or a fixpoint *)
Ltac atomic x :=
  idtac;
  match x with
    | _ => is_evar x; fail 1 x "is not atomic (evar)"
    | ?f _ => fail 1 x "is not atomic (application)"
    | (fun _ => _) => fail 1 x "is not atomic (fun)"
    | forall _, _ => fail 1 x "is not atomic (forall)"
    | let x := _ in _ => fail 1 x "is not atomic (let in)"
    | match _ with _ => _ end => fail 1 x "is not atomic (match)"
    | _ => is_fix x; fail 1 x "is not atomic (fix)"
    | context[?E] => (* catch-all *) (not constr_eq E x); fail 1 x "is not atomic (has subterm" E ")"
    | _ => idtac
  end.

(** Coq's built in tactics don't work so well with things like [iff]
    so split them up into multiple hypotheses *)
(** We do some hackery with typeclasses to get around the fact that
    Coq 8.4 doesn't have tactics in terms; we want to say
<<
Ltac make_apply_under_binders_in lem H :=
  let tac := make_apply_under_binders_in in
  match type of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              $(let ret' := tac lem Hx in
                                exact ret')$) in
         let ret' := (eval cbv zeta in ret) in
         constr:(ret')
    | _ => let ret := constr:($(let H' := fresh in
                                pose H as H';
                                apply lem in H';
                                exact H')$) in
           let ret' := (eval cbv beta zeta in ret) in
           constr:(ret')
  end.

Ltac apply_under_binders_in lem H :=
  let H' := make_apply_under_binders_in lem H in
  let H'' := fresh in
  pose proof H' as H'';
    clear H;
    rename H'' into H.
>> *)

Class make_apply_under_binders_in_helper {T} (lem : T) {T'} (H : T') {T''} := do_make_apply_under_binders_in_helper : T''.

Class make_apply_under_binders_in_helper_helper {T} (H : T) {T'} (lem : T') {T''} := do_make_apply_under_binders_in_helper_helper : T''.

Hint Extern 0 (make_apply_under_binders_in_helper_helper ?H ?lem)
=> let H' := fresh in
   pose H as H';
     apply lem in H';
     exact H'
           : typeclass_instances.

Ltac make_apply_under_binders_in lem H :=
  match type_of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              _ : make_apply_under_binders_in_helper lem Hx) in
         let ret' := (eval cbv zeta beta delta [do_make_apply_under_binders_in_helper make_apply_under_binders_in_helper] in ret) in
         let retT := type_of ret' in
         let retT' := (eval cbv zeta beta delta [do_make_apply_under_binders_in_helper make_apply_under_binders_in_helper] in retT) in
         constr:(ret' : retT')
    | _ => let ret := constr:(_ : make_apply_under_binders_in_helper_helper H lem) in
           let ret' := (eval cbv beta zeta delta [make_apply_under_binders_in_helper_helper do_make_apply_under_binders_in_helper_helper] in ret) in
           let retT := type_of ret' in
           let retT' := (eval cbv beta zeta delta [make_apply_under_binders_in_helper_helper do_make_apply_under_binders_in_helper_helper] in retT) in
           constr:(ret' : retT')
  end.

Hint Extern 0 (make_apply_under_binders_in_helper ?lem ?H) =>
let ret := make_apply_under_binders_in lem H
in exact ret
   : typeclass_instances.

Ltac apply_under_binders_in lem H :=
  let H' := make_apply_under_binders_in lem H in
  let H'' := fresh in
  pose proof H' as H'';
    clear H;
    rename H'' into H.

Tactic Notation "binder_apply" open_constr(lem) "in" hyp(H) := apply_under_binders_in lem H.

Ltac split_in_context ident proj1 proj2 :=
  repeat match goal with
           | [ H : context[ident] |- _ ] =>
             let H0 := make_apply_under_binders_in proj1 H in
             let H1 := make_apply_under_binders_in proj2 H in
             pose proof H0;
               pose proof H1;
               clear H
         end.

Ltac split_iff := split_in_context iff proj1 proj2.
Ltac split_and := split_in_context and proj1 proj2.

(** Test case for [split_and]. *)
Goal (forall x y, x /\ y) -> True.
Proof.
  intro.
  split_and.
  lazymatch goal with
  | [ H0 : forall x : Prop, Prop -> x, H1 : Prop -> forall x : Prop, x |- True ] => idtac
  end.
  exact I.
Qed.

(** A much faster way to [apply] only one component of a lemma that
    ends with an [and]. *)
Tactic Notation "apply_and" open_constr(hyp) :=
  first [ let H' := make_apply_under_binders_in proj1 hyp in apply H'
        | let H' := make_apply_under_binders_in proj2 hyp in apply H' ].


(** Do something with every hypothesis. *)
Ltac do_with_hyp' tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

(** Rewrite with any applicable hypothesis. *)
Tactic Notation "hyp_rewrite" "*" := do_with_hyp' ltac:(fun H => rewrite H).
Tactic Notation "hyp_rewrite" "->" "*" := do_with_hyp' ltac:(fun H => rewrite -> H).
Tactic Notation "hyp_rewrite" "<-" "*" := do_with_hyp' ltac:(fun H => rewrite <- H).
Tactic Notation "hyp_rewrite" "?*" := repeat do_with_hyp' ltac:(fun H => rewrite !H).
Tactic Notation "hyp_rewrite" "->" "?*" := repeat do_with_hyp' ltac:(fun H => rewrite -> !H).
Tactic Notation "hyp_rewrite" "<-" "?*" := repeat do_with_hyp' ltac:(fun H => rewrite <- !H).
Tactic Notation "hyp_rewrite" "!*" := progress hyp_rewrite ?*.
Tactic Notation "hyp_rewrite" "->" "!*" := progress hyp_rewrite -> ?*.
Tactic Notation "hyp_rewrite" "<-" "!*" := progress hyp_rewrite <- ?*.

Tactic Notation "hyp_setoid_rewrite" "*" := do_with_hyp' ltac:(fun H => setoid_rewrite H).
Tactic Notation "hyp_setoid_rewrite" "->" "*" := do_with_hyp' ltac:(fun H => setoid_rewrite -> H).
Tactic Notation "hyp_setoid_rewrite" "<-" "*" := do_with_hyp' ltac:(fun H => setoid_rewrite <- H).
Tactic Notation "hyp_setoid_rewrite" "?*" := repeat do_with_hyp' ltac:(fun H => setoid_rewrite H).
Tactic Notation "hyp_setoid_rewrite" "->" "?*" := repeat do_with_hyp' ltac:(fun H => setoid_rewrite -> H).
Tactic Notation "hyp_setoid_rewrite" "<-" "?*" := repeat do_with_hyp' ltac:(fun H => setoid_rewrite <- H).
Tactic Notation "hyp_setoid_rewrite" "!*" := progress hyp_setoid_rewrite ?*.
Tactic Notation "hyp_setoid_rewrite" "->" "!*" := progress hyp_setoid_rewrite -> ?*.
Tactic Notation "hyp_setoid_rewrite" "<-" "!*" := progress hyp_setoid_rewrite <- ?*.

Tactic Notation "hyp_apply" "*" := do_with_hyp' ltac:(fun H => apply H).
Tactic Notation "hyp_apply" "->" "*" := do_with_hyp' ltac:(fun H => apply -> H).
Tactic Notation "hyp_apply" "<-" "*" := do_with_hyp' ltac:(fun H => apply <- H).
Tactic Notation "hyp_apply" "?*" := repeat do_with_hyp' ltac:(fun H => apply H).
Tactic Notation "hyp_apply" "->" "?*" := repeat do_with_hyp' ltac:(fun H => apply -> H).
Tactic Notation "hyp_apply" "<-" "?*" := repeat do_with_hyp' ltac:(fun H => apply <- H).
Tactic Notation "hyp_apply" "!*" := progress hyp_apply ?*.
Tactic Notation "hyp_apply" "->" "!*" := progress hyp_apply -> ?*.
Tactic Notation "hyp_apply" "<-" "!*" := progress hyp_apply <- ?*.

Tactic Notation "hyp_eapply" "*" := do_with_hyp' ltac:(fun H => eapply H).
Tactic Notation "hyp_eapply" "?*" := repeat do_with_hyp' ltac:(fun H => eapply H).
Tactic Notation "hyp_eapply" "!*" := progress hyp_eapply ?*.


(** Revert all hypotheses *)
Ltac reverse := repeat do_with_hyp' ltac:(fun H => revert H).

(** find the head of the given expression *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

(** Unfolds the head of [expr] *)
Ltac unfold_head expr := let h := head expr in eval unfold h in expr.

(** given a [matcher] that succeeds on some hypotheses and fails on
    others, destruct any matching hypotheses, and then execute [tac]
    after each [destruct].

    The [tac] part exists so that you can, e.g., [simpl in *], to
    speed things up. *)
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:( simpl in * ).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

(** matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(destruct_head_hnf_matcher T).

Ltac destruct_sig_matcher HT :=
  match eval hnf in HT with
    | ex _ => idtac
    | ex2 _ _ => idtac
    | sig _ => idtac
    | sig2 _ _ => idtac
    | sigT _ => idtac
    | sigT2 _ _ => idtac
    | and _ _ => idtac
    | prod _ _ => idtac
  end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.
Ltac destruct_sig' := destruct_all_matches' destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
  destruct_sig_matcher HT || destruct_sig_matcher HT
).

(** if progress can be made by [exists _], but it doesn't matter what
    fills in the [_], assume that something exists, and leave the two
    goals of finding a member of the apropriate type, and proving that
    all members of the appropriate type prove the goal *)
Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists := destruct_head_hnf @sigT;
  match goal with
(*    | [ |- @sig ?T _ ] => destruct_exists' T*)
    | [ |- @sigT ?T _ ] => destruct_exists' T
(*    | [ |- @sig2 ?T _ _ ] => destruct_exists' T*)
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
  end.

(** Run [tac] on the discriminee of a match *)
Ltac do_with_match_discriminee' tac :=
  match goal with
    | [ |- appcontext[match ?E with _ => _ end] ] => tac E
  end.

(** Run [tac] on a hypothesis and the the discriminee of a match in that hypothesis *)
Ltac hyp_do_with_match_discriminee' tac :=
  match goal with
    | [ H : appcontext[match ?E with _ => _ end] |- _ ] => tac H E
  end.

(** Run [elim] on anything that's being discriminated inside a [match] which is also atomic *)
Ltac elim_atomic_in_match' := do_with_match_discriminee' ltac:(fun E => atomic E; elim E).
(** Run [elim] on anything that's being discriminated inside a [match] which is also atomic *)
Ltac generalize_case_atomic_in_match' := do_with_match_discriminee' ltac:(fun E => atomic E; generalize dependent E; case).
(** Run [destruct] on anything that's being discriminated inside a [match] which is also atomic *)
Ltac destruct_atomic_in_match' := do_with_match_discriminee' ltac:(fun E => atomic E; destruct E).
Ltac hyp_destruct_atomic_in_match' := hyp_do_with_match_discriminee' ltac:(fun H E => atomic E; destruct E).

(** [pose proof defn], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type_of defn in
  match goal with
    | [ H : T |- _ ] => fail 1
    | _ => pose proof defn
  end.

(** [pose defn], but only if that hypothesis doesn't exist *)
Tactic Notation "unique" "pose" constr(defn) :=
  match goal with
    | [ H := defn |- _ ] => fail 1
    | _ => pose defn
  end.

(** try to specialize all hypotheses with all other hypotheses.  This
    includes [specialize (H x)] where [H x] requires a coercion from
    the type of [H] to Funclass. *)
Ltac specialize_all_ways :=
  repeat match goal with
           | [ x : ?T, H : _ |- _ ] => unique pose proof (H x)
         end.

(** Run [hnf] in anything inside of a [match] statement *)
Ltac hnf_in_match' :=
  idtac;
  try match goal with
        | [ |- appcontext[match ?E with _ => _ end] ]
          => let E' := (eval hnf in E) in
             progress change E with E'
      end.
Ltac hnf_in_match_in' H :=
  idtac;
  try match type_of H with
        | appcontext[match ?E with _ => _ end]
          => let E' := (eval hnf in E) in
             progress change E with E' in H
      end.

Tactic Notation "hnf_in_match" := do ?progress hnf_in_match'.
Tactic Notation "hnf_in_match" "in" hyp(H) := do ?progress hnf_in_match_in' H.
Tactic Notation "hnf_in_match" "in" "*" := hnf_in_match; do ?do_with_hyp' ltac:(fun H => progress hnf_in_match in H).
Tactic Notation "hnf_in_match" "in" "*" "|-" := do ?do_with_hyp' ltac:(fun H => progress hnf_in_match in H).
Tactic Notation "hnf_in_match" "in" "*" "|-" "*" := hnf_in_match in *.
Tactic Notation "hnf_in_match" "in" hyp(H) "|-" "*" := hnf_in_match; hnf_in_match in H.

(** Run [subst], running [hnf] on any hypothesis that allows [subst]
    to make more progress. *)
Ltac hnf_subst :=
  repeat first [ progress subst
               | do_with_hyp' ltac:(fun H => hnf in H; progress subst) ].

(** [split], but only if the goal is an [and] *)
Ltac split_and_in_goal :=
  match goal with
    | [ |- _ /\ _ ] => idtac
  end;
  split.

(** Run [hnf] underneath one set of binders in [x], eta-expanding once if necessary *)
(** In 8.5, this will be simpler:
<<
Ltac do_under_binders tac term := constr:(fun y => $(let z := tac (term y) in exact z)$).
Ltac hnf_under_binders term := do_under_binders ltac:(fun x => eval hnf in x) term.
>> *)
Class hnf_under_binders_helper {T P} (y : T) (z : P y) := make_hnf_under_binders_helper : P y.
Arguments hnf_under_binders_helper {T P} y z / .
Hint Extern 0 (hnf_under_binders_helper ?y ?z) => let z' := (eval hnf in z) in exact z' : typeclass_instances.

Ltac hnf_under_binders x :=
  let x' := constr:(fun y => _ : hnf_under_binders_helper y (x y)) in
  eval unfold hnf_under_binders_helper in x'.

(** Run [hnf] underneath all binders in [x], eta-expanding as much as possible at top level *)
(** In 8.5, this will be simpler:
<<
Ltac hnf_under_all_binders term :=
  match term with
    | _ => do_under_binders hnf_under_all_binders term
    | _ => eval hnf in term
  end.
>> *)
Class hnf_under_all_binders_helper {T P} (y : T) (z : P y) := make_hnf_under_all_binders_helper : P y.
Arguments hnf_under_all_binders_helper {T P} y z / .
Ltac hnf_under_all_binders x :=
  let x' := match x with
              | _ => constr:(fun y => _ : hnf_under_all_binders_helper y (x y))
              | _ => (eval hnf in x)
            end in
  eval unfold hnf_under_all_binders_helper in x'.
Hint Extern 0 (hnf_under_all_binders_helper ?y ?z) => let z' := hnf_under_all_binders z in exact z' : typeclass_instances.

(** Fail if the goal has an evar *)
Ltac goal_has_evar :=
  idtac;
  match goal with
    | [ |- ?G ] => first [ has_evar G | fail 2 "Goal has no evars" ]
  end.

(** Destruct hypotheses that can be destructed without loosing
    information, such as [and] and [sig]. *)
Ltac destruct_safe_hyps' :=
  first [ progress destruct_head_hnf ex
        | progress destruct_head_hnf and
        | progress destruct_head_hnf prod
        | progress destruct_head_hnf sig
        | progress destruct_head_hnf sig2
        | progress destruct_head_hnf sigT
        | progress destruct_head_hnf sigT2
        | progress hnf_subst ].

Ltac destruct_safe_hyps := repeat destruct_safe_hyps'.

(** Split goals that can be split without loosing
    information, such as [and] and [prod]. *)
Ltac split_safe_goals' :=
  hnf;
  match goal with
    | [ |- and _ _ ] => split
    | [ |- prod _ _ ] => split
  end.

Ltac split_safe_goals := repeat split_safe_goals'.

(** Run [reflexivity], but only if the goal has no evars or one or the other argument is an evar. *)
Ltac evar_safe_reflexivity :=
  idtac;
  match goal with
    | [ |- ?R ?a ?b ]
      => not has_evar R;
        first [ not goal_has_evar
              | is_evar b; unify a b
              | is_evar a; unify a b ]
    | [ |- ?R (?f ?a) (?f ?b) ]
      => not has_evar R;
        not has_evar f;
        first [ is_evar b; unify a b
              | is_evar a; unify a b ]
  end;
  reflexivity.

Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.

Local Open Scope list_scope.
(** Takes two lists, and recursively iterates down their structure, unifying forced evars *)
Ltac unfold_cat lst :=
  match lst with
    | cat ?a ?b => let ab := constr:(app a b) in
                   unfold_cat ab
    | app ?a ?b => let a' := unfold_cat a in
                   let b' := unfold_cat b in
                   constr:(app a b)
    | ?x => constr:(x)
  end.

Ltac norm_list_left lst :=
  let lst0 := unfold_cat lst in
  match lst0 with
    | (?a ++ (?b ++ ?c)) => let lst' := constr:((a ++ b) ++ c) in
                            norm_list_left lst'
    | (?a ++ nil) => norm_list_left a
    | (nil ++ ?a) => norm_list_left a
    | (?a ++ ?b) => let a' := norm_list_left a in
                    let b' := norm_list_left b in
                    constr:(a' ++ b')
    | ?lst' => constr:(lst')
  end.
Ltac norm_list_right lst :=
  let lst0 := unfold_cat lst in
  match lst0 with
    | ((?a ++ ?b) ++ ?c) => let lst' := constr:(a ++ (b ++ c)) in
                            norm_list_right lst'
    | (?a ++ nil) => norm_list_right a
    | (nil ++ ?a) => norm_list_right a
    | (?a ++ ?b) => let a' := norm_list_right a in
                    let b' := norm_list_right b in
                    constr:(a' ++ b')
    | ?lst' => constr:(lst')
  end.

Ltac structurally_unify_lists' l1 l2 :=
  let l1 := unfold_cat l1 in
  let l2 := unfold_cat l2 in
  first [ constr_eq l1 l2
        | is_evar l1; unify l1 l2
        | is_evar l2; unify l2 l1
        | lazymatch l1 with
            | nil => match l2 with
                       | ?a ++ ?b => structurally_unify_lists' l1 a; structurally_unify_lists' l1 b
                       | _ => idtac
                     end
          end
        | lazymatch l2 with
            | nil => match l1 with
                       | ?a ++ ?b => structurally_unify_lists' a l2; structurally_unify_lists' b l2
                       | _ => idtac
                     end
          end
        | let l1l2 := constr:((l1, l2)) in
          match l1l2 with
            | (?a ++ ?b, ?a ++ ?b') => structurally_unify_lists' b b'
            | (?a ++ ?b, ?a' ++ ?b) => structurally_unify_lists' a a'
            | (?a ++ ?b, ?a) => let T := type_of b in structurally_unify_lists' b (nil : T)
            | (?a ++ ?b, ?b) => let T := type_of a in structurally_unify_lists' a (nil : T)
            | (?a, ?a ++ ?b) => let T := type_of b in structurally_unify_lists' (nil : T) b
            | (?b, ?a ++ ?b) => let T := type_of a in structurally_unify_lists' (nil : T) a
          end
        | idtac ].

Ltac structurally_unify_lists l1 l2 :=
  let l1'L := norm_list_left l1 in
  let l2'L := norm_list_left l2 in
  let l1'R := norm_list_right l1 in
  let l2'R := norm_list_right l2 in
  structurally_unify_lists' l1'L l2'L;
    structurally_unify_lists' l1'R l2'R.


(** Unify two terms syntactically, up to evars *)
Class syntax_unify {T} (a : T) (b : T) := unif : a = b.
Hint Extern 0 (syntax_unify ?a ?b) => is_evar a; exact (Coq.Init.Logic.eq_refl a) : typeclass_instances.
Hint Extern 0 (syntax_unify ?a ?b) => is_evar b; exact (Coq.Init.Logic.eq_refl a) : typeclass_instances.
Hint Extern 0 (syntax_unify ?a ?a) => exact (Coq.Init.Logic.eq_refl a) : typeclass_instances.
Hint Extern 1 (syntax_unify (?f ?a) (?f ?b)) => first [ has_evar a | has_evar b ];
                                               let pf := constr:(_ : syntax_unify a b) in
                                               exact (Coq.Init.Logic.eq_refl (f a)) : typeclass_instances.
Hint Extern 1 (syntax_unify (?f ?a) (?g ?a)) => first [ has_evar f | has_evar g ];
                                               let pf := constr:(_ : syntax_unify f g) in
                                               exact (Coq.Init.Logic.eq_refl (f a)) : typeclass_instances.
Hint Extern 2 (syntax_unify (?f ?a) (?g ?b)) => first [ has_evar f | has_evar g ];
                                               first [ has_evar a | has_evar b ];
                                               let pf1 := constr:(_ : syntax_unify f g) in
                                               let pf2 := constr:(_ : syntax_unify a b) in
                                               exact (Coq.Init.Logic.eq_refl (f a)) : typeclass_instances.
Ltac syntax_unif_under_binders A f g :=
  first [ has_evar f | has_evar g ];
  let T := constr:(fun x : A => syntax_unify (f x) (g x)) in
  let T' := (eval cbv beta in T) in
  let pf := constr:(fun x => _ : T' x) in
  exact (Coq.Init.Logic.eq_refl f).
Hint Extern 1 (syntax_unify (fun x : ?A => x) ?g) => syntax_unif_under_binders A (fun x : A => x) g : typeclass_instances.
Hint Extern 1 (syntax_unify ?f (fun x : ?A => x)) => syntax_unif_under_binders A f (fun x : A => x) : typeclass_instances.
Hint Extern 1 (syntax_unify (fun x : ?A => @?f x) ?g) => syntax_unif_under_binders A f g : typeclass_instances.
Hint Extern 1 (syntax_unify ?f (fun x : ?A => @?g x)) => syntax_unif_under_binders A f g : typeclass_instances.
Ltac syntax_unify a b := first [ let unif := constr:(_ : syntax_unify a b) in idtac | fail 1 "The terms" a "and" b "do not unify syntactically" ].

(** Run [reflexivity], but only if the terms are syntactically equal up to evars *)
Ltac syntax_unify_reflexivity :=
  idtac;
  lazymatch goal with
    | [ |- ?R ?a ?b ] => syntax_unify a b
  end;
  reflexivity.

(** A variant on [f_equiv] from Coq.Classes.Morphisms which uses a custom tactic instead of reflexivity, and fails in slightly better ways. *)
Ltac f_equiv_using fin_tac :=
 match goal with
  | |- ?R (?f ?x) (?f' _) =>
    let T := type_of x in
    let Rx := fresh "R" in
    evar (Rx : relation T);
    let H := fresh in
    first [ assert (H : (Rx==>R)%signature f f')
          | fail 1 "Cannot find a valid signature relating" f "and" f' "via" R "(possibly because they are dependent functions)" ];
      unfold Rx in *; clear Rx; [ f_equiv_using fin_tac | apply H; clear H; try fin_tac ]
  | |- ?R ?f ?f' =>
    solve [change (Proper R f); eauto with typeclass_instances | fin_tac ]
 end.

Ltac f_equiv' := f_equiv_using syntax_unify_reflexivity; unfold Basics.flip.

(** Like [f_equal], but for more general relations, and only up to syntax matches.  Safer than [f_equiv], but less general. *)
Ltac f_cancel :=
  lazymatch goal with
    | [ |- ?R (?f ?a) (?f ?a') ]
      => let P := constr:(fun H => proper_prf (Proper := _ : Proper (_ ==> R) f) a a' H) in refine (P _)
    | [ |- ?R (?f ?a ?b) (?f ?a' ?b') ]
      => let P := constr:(fun H H' => proper_prf (Proper := _ : Proper (_ ==> _ ==> R) f) a a' H b b' H') in refine (P _ _)
    | [ |- ?R (?f ?a ?b ?c) (?f ?a' ?b' ?c') ]
      => let P := constr:(fun Ha Hb Hc => proper_prf (Proper := _ : Proper (_ ==> _ ==> R) f) a a' Ha b b' Hb c c' Hc) in refine (P _ _ _)
  end;
  unfold Basics.flip;
  try syntax_unify_reflexivity.

(** Log a message in a tactic that returns a constr *)
Class log {T} (x : T) := mklog : True.
Hint Extern 0 (log ?msg) => idtac msg; exact I : typeclass_instances.
Ltac log msg := constr:(_ : log msg).

(** Run a tactic associated with a class underneath binders of [fun] or [forall] *)
Class run_under_binders_helper {tac_cls_T} (tac_cls : tac_cls_T) {T} (term : T) {R} := make_run_under_binders_helper : R.
Ltac run_under_binders tac_cls term :=
  let dummy := log term in
  lazymatch eval cbv beta in term with
    | (fun _ => _) => let ret := constr:(fun x => _ : run_under_binders_helper tac_cls (term x)) in
                      constr:(ret)
    | (forall x, @?P x) => let ret := constr:(fun x => _ : run_under_binders_helper tac_cls (P x)) in
                           constr:(ret)
    | ?term' => constr:(_ : tac_cls _ term' _)
  end.
Hint Extern 0 (run_under_binders_helper ?tac_cls ?term) => let x := run_under_binders tac_cls term in exact x : typeclass_instances.

Ltac do_in_type tac val :=
  let T := type_of val in
  let T' := tac T in
  constr:(val : T').

(** Run a tactic associated with [tacClass] under as many binders as necessary until it succeeds. *)
(** In 8.5, this will be simpler:
<<
Ltac do_under_binders tac term := constr:(fun y => $(let z := tac (term y) in exact z)$).
Ltac do_under_forall_binders tac term :=
  let T := match term with forall x : ?T, @?P x => constr:(T) end in
  let P := match term with forall x, @?P x => constr:(P) end in
  constr:(forall y : T, $(let z := tac (P y) in exact z)$).
Ltac do_under_many_binders_helper under_binders tac term :=
  match term with
    | _ => tac term
    | _ => under_binders ltac:(do_under_many_binders_helper under_binders tac) term
  end.
Ltac do_under_many_binders tac term := do_under_many_binders_helper do_under_binders tac term.
Ltac do_under_many_forall_binders tac term := do_under_many_forall_binders_helper do_under_binders tac term.
>> *)
Ltac do_under_binders tacClass term := constr:(fun y => _ : tacClass _ (term y) _).
Ltac do_under_forall_binders tacClass term :=
  let T := match term with forall x : ?T, @?P x => constr:(T) end in
  let P := match term with forall x, @?P x => constr:(P) end in
  constr:(forall y : T, (_ : tacClass _ (P y) _)).
Class do_under_many_binders_class {tacClassT} (tacClass : tacClassT) {T} (term : T) {retT} := make_do_under_many_binders : retT.
Ltac do_under_many_binders tacClass term :=
  let tacClass_head := head tacClass in
  let ret := match (eval cbv beta delta [tacClass_head do_under_many_binders_class] in term) with
               | ?term' => constr:(_ : tacClass _ term' _)
               | ?term' => do_under_binders (@do_under_many_binders_class _ tacClass) term'
             end in
  eval cbv beta delta [tacClass_head do_under_many_binders_class] in ret.
Hint Extern 0 (do_under_many_binders_class ?tacClass ?term)
=> let ret := do_under_many_binders tacClass term in exact ret : typeclass_instances.

Class do_under_many_forall_binders_class {tacClassT} (tacClass : tacClassT) {T} (term : T) {retT} := make_do_under_many_forall_binders : retT.
Ltac do_under_many_forall_binders tacClass term :=
  let tacClass_head := head tacClass in
  let ret := match (eval cbv beta delta [tacClass_head do_under_many_forall_binders_class] in term) with
               | ?term' => constr:(_ : tacClass _ term' _)
               | ?term' => do_under_forall_binders (@do_under_many_forall_binders_class _ tacClass) term'
             end in
  eval cbv beta delta [tacClass_head do_under_many_forall_binders_class] in ret.
Hint Extern 0 (do_under_many_forall_binders_class ?tacClass ?term)
=> let ret := do_under_many_forall_binders tacClass term in exact ret : typeclass_instances.

(** Switch the order of the [match] so that we force binders first *)
Class do_under_all_binders_class {tacClassT} (tacClass : tacClassT) {T} (term : T) {retT} := make_do_under_all_binders : retT.
Ltac do_under_all_binders tacClass term :=
  let tacClass_head := head tacClass in
  let ret := match (eval cbv beta delta [tacClass_head do_under_all_binders_class] in term) with
               | ?term' => do_under_binders (@do_under_all_binders_class _ tacClass) term'
               | ?term' => constr:(_ : tacClass _ term' _)
             end in
  eval cbv beta delta [tacClass_head do_under_all_binders_class] in ret.
Hint Extern 0 (do_under_all_binders_class ?tacClass ?term)
=> let ret := do_under_all_binders tacClass term in exact ret : typeclass_instances.

Class do_under_all_forall_binders_class {tacClassT} (tacClass : tacClassT) {T} (term : T) {retT} := make_do_under_all_forall_binders : retT.
Ltac do_under_all_forall_binders tacClass term :=
  let tacClass_head := head tacClass in
  let ret := match (eval cbv beta delta [tacClass_head do_under_all_forall_binders_class] in term) with
               | ?term' => do_under_forall_binders (@do_under_all_forall_binders_class _ tacClass) term'
               | ?term' => constr:(_ : tacClass _ term' _)
             end in
  eval cbv beta delta [tacClass_head do_under_all_forall_binders_class] in ret.
Hint Extern 0 (do_under_all_forall_binders_class ?tacClass ?term)
=> let ret := do_under_all_forall_binders tacClass term in exact ret : typeclass_instances.

Section test_do_under_many_binders.
  Let a := True.
  Let b := a.
  Let c := b.

  Ltac help_unfold_head term :=
    match eval cbv beta in term with
      | ?f ?x => let f' := help_unfold_head f in
                 constr:(f' x)
      | a     => constr:(a)
      | ?term' => let term'' := (eval unfold term' in term') in
                  help_unfold_head term''
      | ?term' => constr:(term')
    end.

  Class unfolder_helper {T} (term : T) {retT : Type} := make_unfolder_helper : retT.
  Hint Extern 0 (unfolder_helper (True -> ?term)) => let term' := help_unfold_head term in
                                                     exact (True -> term')
                                                     : typeclass_instances.

  Ltac unfold_until_a term := do_under_many_binders (@unfolder_helper) term.
  Ltac unfold_forall_until_a term := do_under_many_forall_binders (@unfolder_helper) term.

  Goal True.
    let term := constr:(fun (_ _ _ _ : Set) => True -> c) in
    let ret := unfold_until_a term in
    constr_eq ret ((fun (_ _ _ _ : Set) => True -> a) : Set -> Set -> Set -> Set -> Prop);
      pose ret as ret0.
    let term := constr:(forall _ _ _ _ : Set, True -> c) in
    let ret := unfold_forall_until_a term in
    constr_eq ret ((forall (_ _ _ _ : Set), True -> a) : Prop);
      pose ret as ret1.
  Abort.
End test_do_under_many_binders.

Ltac simpl_paths :=
  repeat
    match goal with
      | [ |- _ = _ :> _ * _ ] => apply injective_projections
      | [ H : _ = _ :> _ * _ |- _ ] => apply paths_prod in H; destruct H
    end.

Ltac hyp_simpl_paths :=
  repeat
    match goal with
      | [ H : _ = _ :> _ * _ |- _ ] => apply paths_prod in H; destruct H
    end.

(** Take goals like [(A -> B) -> (A -> C)] and turn them into goals like [A -> B -> C] *)
Ltac simpl_impl' :=
  idtac;
  match goal with
    | [ |- (forall x : ?A, @?B x) -> (forall x : ?A, @?C x) ] => apply (@specialize_forall A B C) => ?
    | [ |- (exists x : ?A, @?B x) -> (exists x : ?A, @?C x) ] => apply (@specialize_ex A B C) => ?
    | [ |- ?a -> ?b ] => let a' := (eval hnf in a) in
                         let b' := (eval hnf in b) in
                         progress change (a' -> b'); simpl_impl'
    | [ |- _ ] => progress hnf; simpl_impl'
  end.

Ltac simpl_impl := do ?simpl_impl'.

(** Apply [functional_extensionality], introducing variable x. *)

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality) ; intro x
  end.
