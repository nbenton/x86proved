(** * Auxiliary lemmas and tactics for Hoare triples on *programs* *)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.spectac x86proved.safe x86proved.pointsto x86proved.cursor x86proved.x86.instr x86proved.reader x86proved.x86.instrcodec.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import x86proved.x86.program x86proved.x86.basic x86proved.charge.ilogic.
Require Import x86proved.common_tactics x86proved.chargetac.

(** Morphism for program equivalence *)
Global Instance basic_progEq_m :
Proper (lequiv ==> progEq ==> lequiv ==> lequiv) (@basic _ _).
  Proof.
    move => P P' HP c c' Hc Q Q' HQ. split.
    setoid_rewrite -> HQ. setoid_rewrite HP. 
    unfold basic. by setoid_rewrite Hc.
    setoid_rewrite <- HQ. setoid_rewrite <- HP. 
    unfold basic. by setoid_rewrite <-Hc.
  Qed.

(** Skip rule *)
Lemma basic_skip P: |-- @basic _ _ P prog_skip P.
Proof.
  rewrite /basic. specintros => i j. unfold_program.
  specintro => ->. autorewrite with push_at. by apply limplValid. 
Qed.

(** Sequencing rule *)
Lemma basic_seq (c1 c2: program) S P Q R:
  S |-- basic P c1 Q ->
  S |-- basic Q c2 R ->
  S |-- basic P (c1;; c2) R.
Proof.
  move=> Hc1 Hc2. rewrite /basic. 
  specintros => i j. unfold_program. specintro => i'.  
  superspecapply Hc1.
  superspecapply Hc2.
  finish_logic_with sbazooka.
Qed.

(** Scoped label rule *)
Lemma basic_local S P c Q:
  (forall l, S |-- @basic _ _ P (c l) Q) ->
  S |-- @basic _ _ P (prog_declabel c) Q.
Proof.
  move=> H. rewrite /basic. rewrite /memIs /=. specintros => i j l.
  specialize (H l). lforwardR H.
  - apply lforallL with i. apply lforallL with j. reflexivity.
  apply H.
Qed.

(** Needed to avoid problems with coercions *)
Require Import writer roundtrip.
Lemma basic_instr S P i Q :
  S |-- @basic _ _ P i Q ->
  S |-- @basic _ _ P (prog_instr i) Q.
Proof. done. Qed.

Lemma basic_data {T} {R: Reader T} {W: Writer T} {RT: Roundtrip R W} S P (d:T) Q :
  S |-- @basic _ _ P d Q ->
  S |-- @basic _ _ P (prog_data _ d) Q.
Proof. done. Qed.

(** ** Automated application of basic lemmas *)
(** We now develop some tactics for automatically applying relevant
    [basic] lemmas to goals.  The overarching structure consists of
    the following steps:

    0. Pre-format the goal.  This consists of removing things that
       will get in the way of the tactic machinery; it consists of, at
       least, unfolding and introduction.  This step is different for
       structured and unstructured code.  This step is controlled by a
       hint database; see the relevant section below.  Only
       introductions and unfoldings that are suitable for all goals
       should go here.  All evars will be hidden when rewriting; no
       unsafe evar instantiations will be performed.

    1. Locate the current step of the program by peeling off
       sequencing; we do that for [basic] goals in this file, and, at
       the time of the writing of this documentation, we do it for
       unstructured programs in basicseptac.v.  The current step
       should always be atomic; if you have a rule that applies to a
       sequence of instructions, you should give a name to that
       sequence of instructions, make the rule be about that name, and
       never unfold that name in programs you write.

    2. Use typeclass resolution to pick up the rule for the current
       instruction.  

       To get the tactics to pick up, e.g., an induction hypothesis,
       you must inform the machinery that you want it to use your
       hypotheses.  To do this, you [instrrule remember IHn] (or
       whatever your hypothesis is called).

       TODO: Should we automatically remember all relevant hyptoheses
             at the beginning?  That's probably trying to be too
             smart, but maybe we want a tactic that pulls out all the
             hypotheses that talk about [basic], and do [unique pose
             proof] on the relevant instrrule?

    3. Format the rule for application.  The unfoldings that happen in
       this step should be the same as the ones in step 0, so that the
       types will line up nicely.  Warning: This step may leave side
       conditions.

    4. Apply helper lemmas to isolate the current instruction and
       generalize the pre- and post- conditions.  These are generally
       lemmas about sequencing and weakening.

    5. Apply the relevant rule.  It should apply exactly at this step.

    6. Solve the side conditions, or attempt to do so.  This step is
       configurable at the top level; the [strict *] tactics will fail
       with error messages if side conditions cannot be fully solved.
       The default is to error only when the simplification tactics
       leave remaining evars.  The [attempt *] tactics will attempt to
       make progress, and never fail if the rule applies.  The [simple
       *] tactics will not do anything on the side conditions.  The
       [attempt strict *] tactics will only alter side conditions that
       can be fully solved, but will not error if there are remaining
       side conditions.

    The preferred way of working is to do all of the necessary
    rewriting before you run [basic apply *], and to never use
    [attempt basic apply *] except when figuring out what rewriting is
    left to do.  For convenience, the tactic
    [basic_side_conditions] will run side-condition-solving
    code of [basic apply *] on the current goal, allowing you to see
    what would happen had you done the relevant rewriting earlier.  It
    is possible, though disadvised, to leave this tactic in final
    proof scripts.

    To debug a failure of these tactics, you should run each piece
    separately; figure out if it's preformatting that's failing (or
    looping), or finding the relevant instruction, or rule lookup, or
    rule application, or side condition solving.  I've tried to make
    the error messages helpful, but I'm sure they will fall short.

    Each individual tactic should either have a well-specified and
    obvious behavior (in which case it's ok to use Ltac black magic,
    because when it goes wrong, it'll be obvious what it should be
    doing), or should be a general brute-force tactic, in which case
    it should have simple logic (preferably a single [repeat match
    goal with ...] or similar), to which one can easily add or remove
    whatever cases are necessary.

    All tactics should give reasonable error messages; if you use the
    high-level tactic and get an low-level message about no matching
    case for a goal or no applicable tactic, this is a bug in the
    basicprog tactics.

    *** Debugging

    An invocation to [basic apply *] is roughly equivalent to first
    running [simple basic apply *], and then running the following on
    each relevant goal:
<<
  try solve_simple_basicapply;
  progress_side_conditions_basicapply;
  instrrules_check_side_conditions_safe.
>>

    The call to [simple basic apply *] is equivalent to
<<
  instrrule_pre_format_goal;
  let R := get_next_instrrule_for_basic in
  let Hlem := fresh "Hlem" in
  instrrule pose R as Hlem;
  simple basic apply Hlem.
>>

    Running each of these tactics separately should provide enough of
    a hint of where things might be going wrong.  The most likely
    culprit tends to be the side condition handling, which can easily
    loop, or be too zealous, or not strong enough. *)

(** *** Pre-formatting the goal *)
(** We use the [instrrule_all] databases for unfolding and
    rewriting that is safe for all goals. *)
(** It is nice to include justification for the rules in the
    databases.  Invariably, we will fall short of this ideal.  Here
    are the reasons for the hints included at the time this
    documentation was last updated:

    - Unfolding

      - [not] - it was here in the olden days

    - Rewriting

      - [spec_at_basic] - it is convenient to spec things using [@],
        but annoying to use them; we must push the [@]s inside the
        lemmas.  This is slow, so we use
        [spec_at_basic_directionalized] instead, which is twice as
        fast.  We manually specify one direction for the goal, and the
        other direction for the hypotheses, again for speed.  *)

Create HintDb instrrules_all.
Create HintDb instrrules_hyp_all.
Hint Unfold not : instrrules_all.
Hint Rewrite <- @spec_at_basic_directionalized1 : instrrules_all.
Hint Rewrite -> @spec_at_basic_directionalized2 : instrrules_hyp_all.

Ltac instrrule_pre_format_goal :=
  do ?[ set_evars; progress autorewrite with instrrules_all; subst_evars
      | progress autounfold with instrrules_all
      | progress cbv beta iota zeta
      | ((** This won't unfold things ([move => *] sometimes will, I think), but will give unusable names to hypotheses, unlike [intros] *)
        (test progress intros); move => ?) ].

(** *** Locating the current instruction *)

(** We use a type class to ask for a rule for a given instruction,
    parameterized _only_ on the arguments it needs to reduce to
    something of the form [|-- basic ...], and the things that appear
    in the instr. *)
Class instrrule {T} (instr : T) {ruleT} := make_instrrule : ruleT.
Definition get_instrrule_of {T} (instr : T) {ruleT} `{x : @instrrule T instr ruleT} : ruleT := x.
Arguments get_instrrule_of {_} _ {_ _}.

(** We add instances from basicprog *)
Instance: instrrule prog_skip := @basic_skip empSP.
Instance: forall c, instrrule (prog_declabel c) := fun c S P => @basic_local S P c.

(** Now we declare internal tactics, which are useful, but not the
    kind of things we should be using when not debugging.  We [Import]
    it so we don't have to qualify names in this file. *)
Module Import BasicProgInternalsLookup.
  (** Get the program out of a goal; useful for looking up which rule to use. *)
  (** Do a separate [lazymatch] and [match] to make sure that the
      correct error message rises to the top; [lazymatch] will
      evaluate to either the [fail 1] tactic or a constr, and then the
      [match] will run the error or return the constr.  *)
  Ltac get_basic_program_from G :=
    let ret := (lazymatch G with
               | _ |-- ?G' => get_basic_program_from G'
               | basic _ ?P _ => constr:(P)
               | ?G' => fail 1 "No program found in" G'
                end) in
    match True with
      | _ => ret
    end.

  (** Get the first instruction from a program *)
  Ltac get_first_instr P :=
    match P with
      | prog_seq ?P' _ => get_first_instr P'
      | prog_instr ?I => constr:(I)
      | @prog_data Instr _ _ _ I => constr:(I)
      | ?P' => constr:(P')
    end.

  (** We have a tactic that unfolds things in instrrules until we see
      something like [|-- basic _ _ _ _].  However, some rules might
      not be of the form [|-- basic _ _ _ _]; we must explicitly
      handle the head of these rules (e.g., [lforall], [limpl]), to
      throw our hands up and say we're not going to do any more
      unfolding. *)
  Ltac unfold_to_basic_rule_helper term :=
    let term' := (eval cbv beta iota zeta in term) in
    match term' with
      | ?f ?x => let f' := unfold_to_basic_rule_helper f in
                 (** We need to invoke the call again in case [f]
                   unfolded to a [λ], and we need to reduce it, but
                   only in the case that [f] changed *)
                 let f'x := (eval cbv beta iota zeta in (f' x)) in
                 match f' with
                   | f => f'x
                   | _ => unfold_to_basic_rule_helper f'x
                 end
      | @ltrue => term'
      | @lfalse => term'
      | @limpl => term'
      | @land => term'
      | @lor => term'
      | @lforall => term'
      | @lexists => term'
      | @spec_reads => term'
      | @spec_at => term'
      | @basic => term'
      | ?term' => let term'' := (eval unfold term' in term') in
                  unfold_to_basic_rule_helper term''
      | ?term' => constr:(term')
    end.

  (** Currently, [Require] without [Import] will include instances.
      So we don't need to export the instances.  This will change in
      8.5.  However, when we move to 8.5, we should be using tactics
      in terms instead; we can update [do_under_many_forall_binders)
      to take a tactic rather than a typeclass, and pass it [ltac:(fun
      H => let x := unfold_to_basic_rule_helper H in exact x)] or
      something.  So this code _should_ break when we move to 8.5.
      If, for whatever reason, you want to stick with the hacky
      typeclasses method of faking tactics in terms (maybe we'll want
      to try to have a version that works in 8.4 and 8.5
      simultaneously?), you can wrap something like [Module
      BasicProgInternalsThatMustBeExported0.] around these class and
      instance declarations, and then [Export
      BasicProgInternalsThatMustBeExported0] at the bottom of this
      file. *)
  (** We really want tactics in terms, but since we're using Coq 8.4,
      not Coq 8.5, we settle for typeclasses. *)
  Class unfold_to_basic_rule_class {T} (term : T) {retT : Type} := make_unfold_to_basic_rule_class : retT.
  Hint Extern 0 (unfold_to_basic_rule_class (@lentails ?Frm ?ILO ?C ?term))
  => let term' := unfold_to_basic_rule_helper term in
     exact (@lentails Frm ILO C term')
     : typeclass_instances.

  Ltac unfold_rule_until_basic rule :=
    let rule' := (eval unfold get_instrrule_of in rule) in
    (** unfold the instance name, if possible *)
    let rule'' := match True with
                    | _ => unfold_head rule'
                    | _ => constr:(rule')
                  end in
    (** Get the original type of the rule, or else we'll end up with [instrrule] rather than the type we want *)
    let T := type_of rule in
    let T' := do_under_many_forall_binders (@unfold_to_basic_rule_class) T in
    constr:(rule'' : T').
End BasicProgInternalsLookup.

(** The high-level method of getting the rule corresponding to an
    instruction.  These tactics are suitable for use in high-level
    debugging, and [get_instrrule_of] can
    be used in other automation, but these should never show up in
    actual proofs. *)

Ltac get_instrrule_of instr :=
  let rule := match True with
                | _ => constr:(get_instrrule_of instr)
                | _ => fail 1 "Could not find a rule for instruction" instr
              end in
  unfold_rule_until_basic rule.

Ltac get_next_instrrule_for_basic :=
  let G := match goal with |- ?G => constr:(G) end in
  let prog := get_basic_program_from G in
  let instr := get_first_instr prog in
  get_instrrule_of instr.

(** *** Remembering local instrrules *)
(** We have a convenience tactic [instrrule remember H] (and
    [instrrule remember H as ident]) for telling the machinery about a
    given local rule.  This is most useful for exposing induction
    hypotheses for consideration by tactics. *)

Module Import BasicProgMemoryInternals.
  (** We have a tactic, which recurses under binders via typeclasses,
      to change something like [|-- basic _ c _ _] into [instrrule c],
      with the appropriate implicit arguments.  Although this will
      tell typeclass resolution about the rule, it's not enough,
      because we need to hide all arguments that can't be instantiated
      just by knowing what code we're working on; we do that later *)

  Class make_basic_instrrule {T} (H : T) {retT} {ret : retT} := dummy_make_basic_instrrule : True.
  Definition change_to_basic_instrrule {T} (H : T) {retT ret} `{@make_basic_instrrule T H retT ret} : retT := ret.
  Arguments change_to_basic_instrrule {T} H {retT ret _} / .
  Ltac change_to_basic_instrrule_helper H :=
    idtac;
    let TH := type_of H in
    (lazymatch eval cbv beta iota zeta in TH with
    | _ |-- ?c
      => (lazymatch c with
         | context[@basic _ _ _ ?code _]
           => exact (I : @make_basic_instrrule _ H (instrrule code) H)
         | context[@basic _ _ _ _ _] => fail "Code in expression" c "depends on binders introduced under the entailment in rule" H
         | _ => fail "Could not find a basic block of code in" c "in rule" H
          end)
    | forall x : ?T, @?f x
      => let rule := constr:(fun x : T => change_to_basic_instrrule (H x)) in
         exact (I : @make_basic_instrrule _ H _ rule)
    | ?T => fail "Could not make an enailment (lentails) from the type" T "of rule" H
     end).
  Hint Extern 0 (make_basic_instrrule ?H) => change_to_basic_instrrule_helper H : typeclass_instances.
  Ltac get_change_to_basic_instrrule H :=
    let ret := constr:(change_to_basic_instrrule H) in
    let T := type_of ret in
    let ret' := (eval cbv beta iota zeta delta [change_to_basic_instrrule] in ret) in
    constr:(ret' : T).

  (** Now we have the tactics that remove binders that don't show up
      in the code segment.  We make use of Coq's facilities for
      occurence checking and hypothesis reordering by giving ourselves
      a clean goal, introducing all the binders from the instrrule
      hypothesis, and repeatedly reverting binders and shoving them
      into the return type, until there are no revertable binders.  We
      then play tricks with evars to communicate this type to another
      goal, and subsequently materialize an inhabitant of this type by
      applying our original instrrule after introducing enough things.
      We then use [eassumption] to solve the remaining arguments.
      It's rather painful, and all just to change the type of a
      hypothesis. *)

  Class clean_instrrule_helper_type {T} (R : T) := dummy_clean_instrrule_helper_type : Type.
  Ltac instrrule_code_is_accessible :=
    idtac;
    match goal with
      | [ |- context[@instrrule _ ?c _] ] => test pose c
    end.
  Ltac update_instrrule_code :=
    idtac;
    let G := match goal with |- ?G => constr:(G) end in
    (lazymatch G with
    | @instrrule _ _ _ => fail "No quantifier in goal" G
    | forall x : ?A, @instrrule ?T ?R (@?ret x)
      => change (@instrrule T R (forall x : A, ret x))
    | forall x : ?A, @instrrule _ _ _
      => fail "Code depends on binder in" G
    | _ => fail "Goal not of the form forall x, @instrrule _ _ _ :" G
     end).
  Ltac make_clean_instrrule_helper_type orig_rule :=
    generalize orig_rule; clear;
    let IH := fresh "IH" in
    intro IH;
      let T := fresh "T" in
      evar (T : Type);
        let ruleT := type_of IH in
        let newRule := fresh "newT" in
        assert (newRule : ruleT)
          by (intros;
              repeat match goal with
                       | [ H : _ |- _ ] => (not constr_eq H IH; not constr_eq H T; revert H; update_instrrule_code; cbv beta)
                       | [ H : _ |- _ ] => not constr_eq H IH; not constr_eq H T; revert H
                     end;
              let G := match goal with |- ?G => constr:(G) end in
              let T' := (eval unfold T in T) in
              unify G T';
              let do_apply tac := first [ eapply IH
                                        | intro; tac tac ] in
              do_apply do_apply; eassumption);
          exact T.
  Hint Extern 0 (clean_instrrule_helper_type ?R) => make_clean_instrrule_helper_type R : typeclass_instances.
End BasicProgMemoryInternals.

(** And now the actual tactics *)
Ltac instrrule_remember_as rule H :=
  let new_rule := get_change_to_basic_instrrule rule in
  let H' := fresh in
  pose (H' := new_rule);
    let new_type := constr:(_ : clean_instrrule_helper_type H') in
    let new_type' := (eval cbv beta zeta in new_type) in
    assert (H : new_type') by (let do_apply tac := first [ eapply new_rule
                                                         | intro; tac tac ] in
                               do_apply do_apply; eassumption);
      clear H'.
Tactic Notation "instrrule" "remember" open_constr(rule) "as" ident(H) :=
  instrrule_remember_as rule H.
Tactic Notation "instrrule" "remember" open_constr(rule) :=
  let H := fresh in instrrule remember rule as H.

(** *** Isolating the current instruction in the goal *)
(** We first construct the pieces internally; these tactics are meant
    to be semi-modular for easy debugging. *)
Module Import BasicProgInternalsIsolation.
  (** We strip off sequencing and weaken the context. *)

  (** [basicatom] will weaken the context, applying [code_tac] to the
      goal involving [basic], [spec_tac] to the goal involving
      entailment of the hypotheses, and [spred_tac] to the goals involving
      entailment of [SPred]s.  Note that this tactic will fail
      mysteriously if you change the number of arguments of
      [basic] and forget to update the pattern
      matching. *)

  Ltac basic_side_conditions code_tac common_tac spec_tac spred_tac :=
    idtac;
    let G := match goal with |- ?G => constr:(G) end in
    (lazymatch G with
    | @lentails spec _ _ (@basic _ _ _ _ _) => first [ solve [ code_tac ] | fail 1 "Internal error: code tactic did not solve goal" G ]
    | _ => idtac
     end);
      common_tac;
      (lazymatch G with
      | @lentails spec _ _ _                                      => spec_tac
      | @lentails SPred _ _ _                                     => spred_tac
      | @lentails ?x _ _ _                                        => fail 0
                                                                          "The goal is not an entailment of specs nor SPreds but of" x "."
                                                                          "Did you forget to update basicatom when you updated basic_basic_context, basic, or charge's lentails?"
                                                                          "Goal is:" G
      | _ => fail 0
                  "The goal is not an entailment." "Did you forget to update basicatom when you updated charge?"
                  "Goal is:" G
       end).

  Ltac basicatom code_tac common_tac spec_tac spred_tac :=
    eapply basic_basic_context;
    basic_side_conditions code_tac common_tac spec_tac spred_tac.

  (** [basicseq] isolates the current instruction.  If you associate
      instructions the wrong way, you may end up with many goals.  It
      will apply [code_tac] to the goal involving the first
      instruction *)
  Ltac basicseq code_tac :=
    (** We aggregate the arguments to the recursive call for ease of
        use in many places *)
    (** [idtac; ] is a work-around for https://coq.inria.fr/bugs/show_bug.cgi?id=3498 *)
    idtac;
    let rec_tac := basicseq code_tac in
    (idtac;
     lazymatch goal with
     | [ |- _ |-- basic ?P (@prog_instr ?i) ?Q ]
       => (eapply basic_instr; rec_tac)
     | [ |- _ |-- basic ?P (@prog_data _ _ _ _ ?i) ?Q ]
       => (eapply basic_data; rec_tac)
     | [ |- _ |-- basic ?P (prog_seq ?p1 ?p2) ?Q ]
       => (eapply basic_seq; [rec_tac | ]; instantiate; [ .. ])
     | [ |- _ |-- @basic _ _ _ _ _ ] => code_tac
     | [ |- ?G ] => fail "basicseq only handles goals of the form [_ |-- basic _ _ _ _] (and variants of basic), and the current goal is not:" G
     end).
End BasicProgInternalsIsolation.

(** The semi-modular tactic to do something with the first instruction
    in the goal.  First we have a tactic for those who eschew long
    names and context. *)
Ltac handle_first_instruction code_tac common_tac spec_tac spred_tac :=
    basicseq ltac:(basicatom code_tac common_tac spec_tac spred_tac).
(** And now the version that is more future-proof against modifying
    tactics which call it; it has more naming to make it obvious which
    tactic handles what *)
Tactic Notation "denature" "basic" "goal" "then" "do" tactic3(code_tac) "handling"
       "all" "first" "with" tactic3(common_tac)
       "and" "specs" "with" tactic3(spec_tac)
       "and" "SPreds" "with" tactic3(spred_tac)
  := handle_first_instruction code_tac common_tac spec_tac spred_tac.

(** We have some tactics for handling the posing of a given rule to
    apply, and subsequent unfolding and rewriting.

    WARNING: These tactics may leave side conditions. *)
Ltac pose_instrrule_as R H :=
  (have H := R);
  set_evars_in H;
  do ?[ progress autounfold with instrrules_all in H
      | progress autorewrite with instrrules_hyp_all in H
      | progress cbv beta iota zeta in H ];
  eforalls_no_subst_evars H;
  do ?[ progress autounfold with instrrules_all in H
      | progress autorewrite with instrrules_hyp_all in H
      | progress cbv beta iota zeta in H ];
  subst_evars.
Tactic Notation "instrrule" "pose" open_constr(rule) "as" ident(H) := pose_instrrule_as rule H.

(** Apply a given rule to the first instruction, and subsequently
    handle the side conditions. *)
Ltac apply_instrrule_to_first_instr_then R common_tac spec_tac spred_tac :=
  let Hlem := fresh "Hlem" in
  instrrule pose R as Hlem;
    first (denature basic goal then
             do (first [ eexact Hlem
                       | let G := match goal with |- ?G => constr:(G) end in
                         let T := type_of Hlem in
                         fail 1 "Could not apply basic rule" T "to goal" G ]) handling
                all first with (common_tac)
                and specs with (spec_tac)
                and SPreds with (spred_tac));
    do [ clear Hlem | idtac "Warning: Could not clear posed hypothesis" Hlem | idtac "Warning: Could not clear posed hypothesis" ].

Tactic Notation "instrrule" "apply" open_constr(R) "to" "first" "basic" "goal" "handling"
       "all" "first" "with" tactic3(common_tac)
       "and" "specs" "with" tactic3(spec_tac)
       "and" "SPreds" "with" tactic3(spred_tac)
  := apply_instrrule_to_first_instr_then R common_tac spec_tac spred_tac.

(** *** Handling side conditions *)
(** When solving side conditions, we want to first attempt to unify
    evars and solve simple things, so that ways in which we transform
    the goal don't unnecessarily effect other goals through evars.
    Once we've done all we can, then we want to unfold as much as we
    can, so that we get down to common building blocks that unify.
    For unfolding and rewriting here, we use the
    [instrrules_side_conditions] database.  We have specific databases
    for each of the kinds of side conditions. *)
(** We first populate the databases with redundant things from
    [instrrules_all], so that we don't get error messages about
    missing databases. *)
Create HintDb instrrules_side_conditions.
Create HintDb instrrules_side_conditions_spec.
Create HintDb instrrules_side_conditions_spred.
Hint Unfold not
: instrrules_side_conditions instrrules_side_conditions_spec instrrules_side_conditions_spred.
Hint Unfold stateIsAny : instrrules_side_conditions_spred.
(** [Hint Rewrite] only supports one database at a time in 8.4.  In
    8.5, it'll be nicer and support multiple ones. *)
Hint Rewrite eq_refl : instrrules_side_conditions.
Hint Rewrite <- @spec_at_basic_directionalized1 : instrrules_side_conditions_spec.
Hint Rewrite low_catB addB0 add0B : instrrules_side_conditions_spred.

Module Import BasicProgInternalsSideConditions.
  (** Apparently [set_evars; progress rewrite 
  -> ?empSPL, -> ?empSPR; subst_evars] is rather slow.  So we
  special-case the ones we care about. *)
  Ltac rewrite_emp :=
    repeat match goal with
             | [ |- _ |-- ?A ** empSP ] => (etransitivity; [ | exact (proj2 (empSPR A)) ])
             | [ |- ?A ** empSP |-- _ ] => (etransitivity; [ exact (proj1 (empSPR A)) | ])
             | [ |- _ |-- empSP ** ?A ] => (etransitivity; [ | exact (proj2 (empSPL A)) ])
             | [ |- empSP ** ?A |-- _ ] => (etransitivity; [ exact (proj1 (empSPL A)) | ])
           end.

  (** A tactic for solving the side conditions when the basicapplied lemma is completely unconstrained. *)
  Ltac simplify_basicapply_side_condititions_with' tac :=
    do [ ((** Try to solve the goal by [reflexivity], but not if it's
              going to instantiate evars too eagerly (and maybe
              wrongly), nor if it's going to take forever to unify
              things *)
           evar_safe_syntax_unify_reflexivity)
       | idtac;
         match goal with
           | [ |- _ |-- ltrue ] => solve [ apply ltrueR ]
           | [ |- lfalse |-- _ ] => solve [ apply lfalseL ]
         end
       | progress rewrite_emp
       | progress tac ].

  Ltac simplify_basicapply_side_condititions_with tac := do ?simplify_basicapply_side_condititions_with' tac.

  Ltac solve_simple_basicapply :=
    solve [ simplify_basicapply_side_condititions_with
              ltac:(idtac;
                    match goal with
                      (** If we [basicapply] a lemma that's too
                          general (has unrestricted pre- and post-
                          conditions), then we end up with goals like
                          [P |-- ?1 ** ?2] and [?3 ** ?2 |-- Q].  We
                          need to instantiate [?1] with [P], [?2] with
                          [empSP], and [?3] with [Q].  We would like
                          to just [rewrite -> empSPR; reflexivity],
                          but Coq might decide that I mean to say that
                          [?1] is [?4 ** empSP], and might therefore
                          loop if I do [rewrite -> !empSPR], and
                          [reflexivity] might take forever trying to
                          unify inequal terms.  So we handle evars and
                          their locations explicitly.  *)
                      | [ |- ?A |-- ?B ** ?e ] => (is_evar e; etransitivity; [ | exact (proj2 (empSPR B)) ])
                      | [ |- ?A ** ?e |-- ?B ] => (is_evar e; etransitivity; [ exact (proj1 (empSPR A)) | ])
                      | [ |- ?A |-- ?B ** empSP ] => (etransitivity; [ | exact (proj2 (empSPR B)) ])
                      | [ |- ?A ** empSP |-- ?B ] => (etransitivity; [ exact (proj1 (empSPR A)) | ])
                    end) ].

  Ltac instrrules_default_common_side_conditions_with early_tac late_tac :=
    (** Order matters!  We must first try to solve the evars we can,
        and only later unfold things. *)
    do ?[ solve_simple_basicapply
        | progress early_tac
        | progress simplify_basicapply_side_condititions_with' idtac
        | progress eauto with nocore instrrules_all instrrules_side_conditions nocore
        | progress ssimpl
        | progress autounfold with instrrules_all instrrules_side_conditions
        | set_evars; progress autorewrite with instrrules_all instrrules_side_conditions; subst_evars
        | progress late_tac
        | progress sbazooka ].

  (** We say that a side condition is safe to leave to the user if it
      has no evars *)
  Ltac instrrules_check_side_conditions_safe_failing_with err :=
    do [ not goal_has_evar
       | idtac;
         let G := match goal with |- ?G => constr:(G) end in
         match G with
           | appcontext[?e]
             => (is_evar e;
                 let T := type_of e in
                 err G e T)
           | _ => fail 2
                       "Instrrules Anomaly: tactics disagree on whether or not the goal has an evar."
                       "Probably a bug in the [goal_has_evar] tactic or the [not] tactical."
                       "Alternatively, the tactic passed to instrrules_check_side_conditions_safe_failing_with failed at level 0."
                       "Goal was:" G
         end
       | fail 1 "Instrrules Error: The tactic passed to instrrules_check_side_conditions_safe_failing_with failed at level 1." ].
End BasicProgInternalsSideConditions.

(** We export the name of this tactic, for ease of debugging. *)
Ltac solve_simple_basicapply := BasicProgInternalsSideConditions.solve_simple_basicapply.

Ltac instrrules_check_side_conditions_safe :=
  instrrules_check_side_conditions_safe_failing_with
    ltac:(fun G e T => fail 2
                            "Could not instantiate all evars in the side condition" G
                            "The evar" e "of type" T "was left uninstantiated."
                            "To get this goal, use the [attempt ] version of the high-level tactic you called."
                            "To get the precursor to this goal, use the [attempt strict ] version of the high-level tactic you called."
                            "To get the precursor to this goal, and goals for all the other side conditions, use the [simple ] version of the high-level tactic you called.").

(** The [pre_] variants of the tactics do everything except for the
    final checking of the side conditions, which is left to the
    high-level tactics which must decide whether to call something
    like [instrrules_check_side_conditions_safe]. *)
Ltac pre_instrrules_default_side_condition_spec :=
  instrrules_default_common_side_conditions_with
    ltac:(progress eauto with nocore instrrules_all instrrules_side_conditions instrrules_side_conditions_spec)
           ltac:(do [ progress autounfold with instrrules_side_conditions_spec
                    | set_evars; progress autorewrite with instrrules_side_conditions_spec; subst_evars ]).
Ltac pre_instrrules_default_side_condition_spred :=
  instrrules_default_common_side_conditions_with
    ltac:(progress eauto with nocore instrrules_all instrrules_side_conditions instrrules_side_conditions_sped)
           ltac:(do [ progress autounfold with instrrules_side_conditions_spred
                    | set_evars; progress autorewrite with instrrules_side_conditions_spred; subst_evars ]).

(** This is a convenience tactic, mostly for debugging purposes *)
Ltac progress_side_conditions_basicapply :=
  basic_side_conditions idtac
                        idtac
                        pre_instrrules_default_side_condition_spec
                        pre_instrrules_default_side_condition_spred.
                        

(** This is a convenience tactic, for debugging and developing purposes. *)
Ltac basic_side_conditions :=
  try solve_simple_basicapply;
  progress_side_conditions_basicapply.


(** *** Putting it all together *)
(** Finally, we have the tactics that combine the above pieces to
    apply various lemmas. *)
(** First, we have the [basicapply] tactics which take lemmas. *)
Ltac do_basicapply R common_tac spec_tac spred_tac :=
  instrrule_pre_format_goal;
  instrrule apply R to first basic goal handling
            all first with (common_tac)
            and specs with (spec_tac)
            and SPreds with (spred_tac).

(** For convenience, we make a variant that passes the default tactic to the given tacticals. *)
Ltac do_basicapply_wrap R common_tac spec_tac spred_tac :=
  do_basicapply R
                ltac:(common_tac ltac:(try solve_simple_basicapply))
                ltac:(spec_tac pre_instrrules_default_side_condition_spec)
                ltac:(spred_tac pre_instrrules_default_side_condition_spred).

(** For convenience, we make a variant that appends the given tactics to the defaults. *)
Ltac do_basicapply_append R common_tac spec_tac spred_tac :=
  do_basicapply_wrap R
                     ltac:(fun tac => tac; common_tac)
                     ltac:(fun tac => tac; spec_tac)
                     ltac:(fun tac => tac; spred_tac).

Ltac do_basicapply_append_all R common_tac all_tac :=
  do_basicapply_append R common_tac all_tac all_tac.

Ltac do_basicapply_wrap_all R common_tac all_tac :=
  do_basicapply_wrap R common_tac all_tac all_tac.

Tactic Notation "general" "basic" "apply" open_constr(R) "side" "conditions"
       "all" "first" tactic3(common_tac)
       "and" "specs" tactic3(spec_tac)
       "and" "SPreds" tactic3(spred_tac)
  := do_basicapply R common_tac spec_tac spred_tac.
Tactic Notation "general" "basic" "apply" open_constr(R) "side" "conditions" "append"
       "all" "first" tactic3(common_tac)
       "and" "specs" tactic3(spec_tac)
       "and" "SPreds" tactic3(spred_tac)
  := do_basicapply_append R common_tac spec_tac spred_tac.

Tactic Notation "basic" "apply" open_constr(R)
  := do_basicapply_append_all R idtac instrrules_check_side_conditions_safe.

Tactic Notation "attempt" "basic" "apply" open_constr(R)
  := do_basicapply_append_all R idtac idtac.

Tactic Notation "strict" "basic" "apply" open_constr(R)
  := do_basicapply_wrap_all R ltac:(fun tac => tac)
                                     ltac:(fun tac => first [ solve [ tac ]
                                                            | let G := match goal with |- ?G => constr:(G) end in
                                                              fail 1
                                                                   "Could not fully solve all side conditions."
                                                                   "Invoke attempt strict basic apply" R "to proceed anyway."
                                                                   "A remaining side condition:" G ]).

Tactic Notation "attempt" "strict" "basic" "apply" open_constr(R)
  := do_basicapply_wrap_all R ltac:(fun tac => tac) ltac:(fun tac => try solve [ tac ]).

Tactic Notation "simple" "basic" "apply" open_constr(R)
  := do_basicapply_wrap_all R ltac:(fun _ => idtac) ltac:(fun _ => idtac).


(** Now we have the variants that first materialize the relevant rule. *)
Tactic Notation "general" "basic" "apply" "*" "side" "conditions"
       "all" "first" tactic3(common_tac)
       "and" "specs" tactic3(spec_tac)
       "and" "SPreds" tactic3(spred_tac)
  := instrrule_pre_format_goal;
    let R := get_next_instrrule_for_basic in
    general basic apply (R) side conditions
            all first (common_tac)
            and specs (spec_tac)
            and SPreds (spred_tac).
Tactic Notation "general" "basic" "apply" "*" "side" "conditions" "append"
       "all" "first" tactic3(common_tac)
       "and" "specs" tactic3(spec_tac)
       "and" "SPreds" tactic3(spred_tac)
  := instrrule_pre_format_goal;
    let R := get_next_instrrule_for_basic in
    general basic apply (R) side conditions append
            all first (common_tac)
            and specs (spec_tac)
            and SPreds (spred_tac).

Tactic Notation "basic" "apply" "*"
  := instrrule_pre_format_goal; let R := get_next_instrrule_for_basic in basic apply R.

Tactic Notation "attempt" "basic" "apply" "*"
  := instrrule_pre_format_goal; let R := get_next_instrrule_for_basic in attempt basic apply R.

Tactic Notation "strict" "basic" "apply" "*"
  := instrrule_pre_format_goal;
    let R := get_next_instrrule_for_basic in
    do_basicapply_wrap_all R ltac:(fun tac => tac)
                                    ltac:(fun tac => first [ solve [ tac ]
                                                           | let G := match goal with |- ?G => constr:(G) end in
                                                             fail 1
                                                                  "Could not fully solve all side conditions when applying rule" R "."
                                                                  "Invoke attempt strict basic apply * to proceed anyway."
                                                                  "A remaining side condition:" G ]).

Tactic Notation "attempt" "strict" "basic" "apply" "*"
  := instrrule_pre_format_goal; let R := get_next_instrrule_for_basic in attempt strict basic apply R.

Tactic Notation "simple" "basic" "apply" "*"
  := instrrule_pre_format_goal; let R := get_next_instrrule_for_basic in simple basic apply R.



