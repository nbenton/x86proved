Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.SPred x86proved.septac x86proved.spec x86proved.spectac x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.basic x86proved.x86.macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.

Definition xorSwapImpl (r1 r2: Reg) : program :=
  XOR r1, r2;;
  XOR r2, r1;;
  XOR r1, r2.

Definition tmpSwapImpl (r1 r2 rt: Reg) : program :=
  MOV rt, r1;;
  MOV r1, r2;;
  MOV r2, rt.

(* Spec that is "common" between the two implementations *)
(* We use "@" to conjoin implementation-specific scratch usage *)
Definition basicSwap (r1 r2: Reg) c :=
  Forall v, Forall w,
  basic
  (r1 ~= v ** r2 ~= w)
  c empOP
  (r1 ~= w ** r2 ~= v).

Lemma xorSwapCorrect (r1 r2: Reg) :
  |-- basicSwap r1 r2 (xorSwapImpl r1 r2) @ OSZCP?.
Proof.
  rewrite /xorSwapImpl/basicSwap. specintros => v w. autorewrite with push_at.
  change (stateIs (RegOrFlagR (regToAnyReg ?a))) with (@DWORDorBYTEregIs true a).

  (* XOR r1, r2 *)
  (** The fact that we need to explicitly give [true] here is
      annoying.  If we don't give [true], Coq, ignoring any requests
      we make about the opacity of [basic], takes forever trying and
      failing to unify two terms involving [basic] because it can't
      tell, from trying to unify [if ?1 then A else B] with [A] that
      [?1] should be [true].  This is because we don't properly handle
      [DWORDorBYTE] in [InstrArg], and use the hackish
      [InstrArg_of_DWORDorBYTEReg] *)
  eapply basic_seq; [try done | |].
  basicapply (@XOR_RR_rule true).

  (* XOR r2, r1 *)
  try_basicapply (@XOR_RR_rule true); rewrite /stateIsAny/OSZCP; sbazooka.

  (* XOR r1, r2 *)
  try_basicapply (@XOR_RR_rule true); rewrite /stateIsAny/OSZCP; sbazooka.

  (* Now we're left reasoning about XOR *)
  rewrite /DWORDorBYTEregIs.
  rewrite {2}[X in xorB w X]xorBC.
  rewrite [X in r2~=X]xorBA.
  autorewrite with bitsHints.
  rewrite [X in xorB _ X]xorBC xorBA.
  by autorewrite with bitsHints.
Qed.

Lemma tmpSwapCorrect (r1 r2 rt: Reg) :
  |-- basicSwap r1 r2 (tmpSwapImpl r1 r2 rt) @ rt?.
Proof.
  rewrite /tmpSwapImpl/basicSwap. specintros => v w. autorewrite with push_at.

  (* Good example where automatic opening and pulling out of existentials would be helpful *)
  (* MOV rt, r1 *)
  basicapply MOV_RanyR_rule.

  (* MOV r1, r2 *)
  basicapply MOV_RR_rule.

  (* MOV r2, r1 *)
  basicapply MOV_RR_rule. rewrite /stateIsAny. sbazooka.
Qed.
