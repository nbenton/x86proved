(** * Macros for dealing with applying [basic] lemmas to less structured code *)
(** Not sure if these should go here or in some other file, or how to
    structure dependencies on being able to unfold things like
    [DWORDorBYTEregIs]... *)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.seq.
Require Import x86proved.bitsrep x86proved.spred x86proved.spec x86proved.septac x86proved.spectac.
Require Import x86proved.x86.reg x86proved.x86.flags (* for EIP *) x86proved.x86.instrrules.core (* for [DWORDorBYTEregIs] *) x86proved.x86.program.
Require Import x86proved.safe x86proved.opred x86proved.obs.
Require Import x86proved.common_tactics.


(** We now have a number of macros for dealing with applying [basic]
    lemmas to less structured code.  We can pull out the [EIP] pointer
    (handling the magic wand case correctly), and figure out which bit
    of code we're on. *)
Ltac locate_reg_component choose_arrow_component G :=
  let locate := locate_reg_component choose_arrow_component in
  match G with
    | _ |-- ?G'           => locate G'
    | ?G' <@ _            => locate G'
    | (?G0 -->> ?G1) @ ?R => let G' := constr:(G0 @ R -->> G1 @ R) in locate G'
    | ?G0 -->> ?G1        => let G' := choose_arrow_component G0 G1 in locate G'
    | _ @ ?G1 @ ?G2       => let G' := constr:(G1 ** G2) in locate G'
    | _ @ ?G'             => locate G'
    | _                   => constr:(G)
  end.
Ltac locate_post_reg_component G := locate_reg_component ltac:(fun G0 G1 => constr:(G1)) G.
Ltac locate_pre_reg_component G := locate_reg_component ltac:(fun G0 G1 => constr:(G0)) G.
Ltac locate_frame G :=
  match G with
    | _ |-- ?G'  => locate_frame G'
    | _ <@ ?F   => constr:(F)
    | _         => fail 2 "No frame in" G
  end.
Ltac locate_regIsReg regIsReg G :=
  match eval cbv beta iota zeta delta [stateIs DWORDorBYTEregIs] in G with
    | regIsReg ?x     => constr:(x)
    | ?a ** _         => locate_regIsReg regIsReg a
    |  _ ** ?b        => locate_regIsReg regIsReg b
    | ?G'             => fail 1 "No (unique)" regIsReg "found in" G'
  end.
Ltac locate_code codeIs F :=
  match F with
    | codeIs ?last ?code => constr:(code)
    | ?a ** _            => locate_code codeIs a
    | _  ** ?b           => locate_code codeIs b
    | ?G'                => fail 1 "No (unique) code at" codeIs "found in" G'
  end.

Ltac locate_reg reg G := let regIsReg := constr:(regIs reg) in locate_regIsReg regIsReg G.

Ltac get_post_reg_from reg G :=
  let G' := locate_post_reg_component G in
  locate_reg reg G'.

Ltac get_pre_reg_from reg G :=
  let G' := locate_pre_reg_component G in
  locate_reg reg G'.

Ltac get_post_reg reg :=
  let G := match goal with |- ?G => constr:(G) end in
  get_post_reg_from reg G.

Ltac get_pre_reg reg :=
  let G := match goal with |- ?G => constr:(G) end in
  get_pre_reg_from reg G.

Ltac get_code_at_from eip G :=
  let G' := (eval cbv beta iota zeta in G) in
  let F := locate_frame G' in
  let codeIs'0 := constr:(@memIs Instr _ eip) in
  let codeIs'1 := constr:(@memIs program _ eip) in
  let codeIs0 := (eval cbv beta iota zeta in codeIs'0) in
  let codeIs1 := (eval cbv beta iota zeta in codeIs'1) in
  match F with
    | _ => locate_code codeIs0 F
    | _ => locate_code codeIs1 F
    | _ => fail 1 "No (unique) code at" codeIs0 "nor at" codeIs1 "found in" F
  end.

(** Get the code located at [EIP] *)
Ltac get_eip_code G :=
  let eip := get_post_reg_from EIP G in
  get_code_at_from (eip : DWORD) G.

Ltac check_eips_match A B :=
  let pre_eip_A := get_pre_reg_from EIP A in
  let post_eip_A := get_post_reg_from EIP A in
  let pre_eip_B := get_pre_reg_from EIP B in
  let post_eip_B := get_post_reg_from EIP B in
  constr_eq pre_eip_A pre_eip_B;
    constr_eq post_eip_A post_eip_B.

Ltac check_goal_eips_match :=
  let pre_eip := get_pre_reg EIP in
  let post_eip := get_post_reg EIP in
  constr_eq pre_eip post_eip.


Ltac split_eip_match :=
  let G := match goal with |- ?G => constr:(G) end in
  let eip := get_post_reg_from EIP G in
  let discriminee := match eip with
                       | context[match ?E with _ => _ end] => constr:(E)
                       | _ => fail 1 "No 'if ... then ... else' nor 'match ... with ... end' found in EIP =" eip
                     end in
  match discriminee with
    | _ => atomic discriminee; destruct discriminee
    | _ => case_eq discriminee => ?
  end;
    clean_case_eq.

(** Pull the current [EIP] code, and specapply the relevant lemma *)
Ltac get_next_instrrule_from_eip :=
  let G := match goal with |- ?G => constr:(G) end in
  let instr := get_eip_code G in
  get_instrrule_of instr.
Ltac get_next_loopy_instrrule_from_eip :=
  let G := match goal with |- ?G => constr:(G) end in
  let instr := get_eip_code G in
  get_loopy_instrrule_of instr.
(** [pre_specapply_any] does some clean up for pulling out the rule. *)
Ltac pre_specapply_any :=
  rewrite /makeBOP/makeUOP/makeMOV;
  cbv beta iota zeta;
  do ?((test progress intros); move => ?).
Tactic Notation "specapply" open_constr(lem) := specapply lem.
Tactic Notation "specapply" "*" :=
  pre_specapply_any;
  let R := get_next_instrrule_from_eip in
  first [ specapply R
        | fail 1 "Failed to specapply basic lemma" R ].
Tactic Notation "loopy_specapply" "*" :=
  pre_specapply_any;
  let R := get_next_loopy_instrrule_from_eip in
  first [ specapply R
        | fail 1 "Failed to specapply basic lemma" R ].
