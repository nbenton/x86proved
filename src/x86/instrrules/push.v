(** * PUSH instruction *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
(* We really only need these Imports
Require Import procstate bitsops.
Require Import spec SPred basic basicprog.
Require Import instr pointsto cursor.
Require Import instrsyntax.*)
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import common_tactics.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

(** Generic rule *)

Lemma PUSH_rule src sp (v:DWORD) :
  |-- specAtSrc src (fun w =>
      basic    (ESP ~= sp    ** sp-#4 :-> v) (PUSH src)
               (ESP ~= sp-#4 ** sp-#4 :-> w)).
Proof. do_instrrule_triple. Qed.

Ltac basicPUSH :=
  let R := lazymatch goal with
             | |- |-- basic ?p (PUSH ?a) ?q => constr:(PUSH_rule a)
           end in
  basicapply R.

(** We open a section in order to localize the hints *)
Section InstrRules.

Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : basicapply.
Hint Rewrite
  addB0 low_catB : basicapply.

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
