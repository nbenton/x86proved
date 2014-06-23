(** * PUSH instruction *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

(* We open a section in order to localize the hints *)
Section InstrRules.

Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : basicapply.
Hint Rewrite
  addB0 low_catB : basicapply.

(*---------------------------------------------------------------------------
    Helpers for pieces of evaluation (adapted from spechelpers and
    triplehelpers)
  ---------------------------------------------------------------------------*)

Hint Unfold
  evalInstr
  evalArithOp evalArithOpNoCarry evalArithUnaryOp evalArithUnaryOpNoCarry
  evalLogicalOp evalBinOp evalShiftOp evalUnaryOp evalCondition
  evalMOV evalDst evalDstR evalDstM evalSrc evalMemSpec evalBYTEReg : eval.

Hint Unfold interpJmpTgt : specapply.

(** Generic rule *)
Lemma PUSH_rule src sp (v:DWORD) :
  |-- specAtSrc src (fun w =>
      basic    (ESP ~= sp    ** sp-#4 :-> v) (PUSH src)
               (ESP ~= sp-#4 ** sp-#4 :-> w)).
Proof.
rewrite /specAtSrc. destruct src.
- apply TRIPLE_basic => R. repeat autounfold with eval.
  triple_apply evalPush_rule.
- rewrite /specAtMemSpec.
  elim: ms => [optSIB offset].
  case: optSIB => [[base indexAndScale] |].
  case: indexAndScale => [[rix sc] |].
  + specintros => oldv pbase indexval.
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply evalPush_rule.
  + specintros => oldv pbase.
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply evalPush_rule.
  + specintros => oldv.
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc/evalMemSpec.
    triple_apply triple_letGetDWORDSep.
    triple_apply evalPush_rule.

- specintros => oldv.
  autorewrite with push_at.
  apply TRIPLE_basic => R.
  rewrite /evalInstr.
  triple_apply triple_letGetRegSep.
  triple_apply evalPush_rule.
Qed.

Ltac basicPUSH :=
  match goal with
  | |- |-- basic ?p (PUSH ?a) ?q => try_basicapply (PUSH_rule a)
  end.

(** ** PUSH r *)
Corollary PUSH_R_rule (r:Reg) sp (v w:DWORD) :
  |-- basic (r ~= v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH r)
            (r ~= v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(** ** PUSH v *)
Corollary PUSH_I_rule (sp v w:DWORD) :
  |-- basic (ESP ~= sp    ** sp-#4 :-> w)
            (PUSH v)
            (ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(** ** PUSH [r + offset] *)
Corollary PUSH_M_rule (r: Reg) (offset:nat) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH [r + offset])
            (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(** ** PUSH [r] *)
Corollary PUSH_M0_rule (r: Reg) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH [r])
            (r ~= pbase ** pbase :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.
End InstrRules.
