(** * INC and DEC instructions *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec OPred triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

(** ** Generic increment/decrement rule *)
Lemma INCDEC_rule d (dir: bool) (src:RegMem d) oldv o s z c pf:
  |-- specAtRegMemDst src (fun V =>
      basic (V oldv ** OSZCP o s z c pf) (if dir then UOP d OP_INC src else UOP d OP_DEC src)
      empOP
      (let w := if dir then incB oldv else decB oldv in
      V w ** OSZCP (msb oldv!=msb w) (msb w) (w == #0) c (lsb w))).
Proof. do_instrrule_triple. Qed.

Definition INC_rule := Eval hnf in @INCDEC_rule true true.
Definition DEC_rule := Eval hnf in @INCDEC_rule true false.

Ltac basicINCDEC :=
  rewrite /makeUOP;
  let R := lazymatch goal with
             | |- |-- basic ?p (@UOP ?d OP_INC ?a) ?O ?q => constr:(@INCDEC_rule d true a)
             | |- |-- basic ?p (@UOP ?d OP_DEC ?a) ?O ?q => constr:(@INCDEC_rule d false a)
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

Hint Unfold OSZCP : spred.

(** Special case for increment register *)
Corollary INC_R_rule (r:Reg) (v:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (INC r) empOP
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Corollary INC_M_rule (r:Reg) (offset:nat) (v pbase:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** OSZCP o s z c pf) (INC [r + offset]) empOP
            (r ~= pbase ** pbase +# offset :-> w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Lemma INC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (INC r) empOP (r~=incB v) @ OSZCP?.
Proof.
  autorewrite with push_at. rewrite /stateIsAny. specintros => o s z c p.
  basicINCDEC.
Qed.

(* Special case for decrement *)
Lemma DEC_R_rule (r:Reg) (v:DWORD) o s z c pf :
  let w := decB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (DEC r) empOP
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Lemma DEC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (DEC r) empOP (r~=decB v) @ OSZCP?.
Proof.
  autorewrite with push_at. rewrite /stateIsAny. specintros => o s z c p.
  basicINCDEC.
Qed.
End InstrRules.
