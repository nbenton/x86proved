(** * Various useful general purpose tactics *)

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
  match type of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              _ : make_apply_under_binders_in_helper lem Hx) in
         let ret' := (eval cbv zeta beta delta [do_make_apply_under_binders_in_helper make_apply_under_binders_in_helper] in ret) in
         let retT := type of ret' in
         let retT' := (eval cbv zeta beta delta [do_make_apply_under_binders_in_helper make_apply_under_binders_in_helper] in retT) in
         constr:(ret' : retT')
    | _ => let ret := constr:(_ : make_apply_under_binders_in_helper_helper H lem) in
           let ret' := (eval cbv beta zeta delta [make_apply_under_binders_in_helper_helper do_make_apply_under_binders_in_helper_helper] in ret) in
           let retT := type of ret' in
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
