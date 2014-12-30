Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.spectac x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor x86proved.x86.basic x86proved.x86.macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.

Definition xorSwapImpl s (r1 r2: GPReg s) : program :=
  XOR r1, r2;;
  XOR r2, r1;;
  XOR r1, r2.

Definition tmpSwapImpl s(r1 r2 rt: GPReg s) : program :=
  MOV rt, r1;;
  MOV r1, r2;;
  MOV r2, rt.

(* Spec that is "common" between the two implementations *)
(* We use "@" to conjoin implementation-specific scratch usage *)
Definition basicSwap s (r1 r2: GPReg s) c :=
  Forall v, Forall w,
  basic
  (r1 ~= v ** r2 ~= w)
  c empOP
  (r1 ~= w ** r2 ~= v).

Lemma xorSwapCorrect s (r1 r2: GPReg s) :
  |-- basicSwap r1 r2 (xorSwapImpl r1 r2) @ OSZCP?.
Proof.
  rewrite /xorSwapImpl/basicSwap. specintros => v w. autorewrite with push_at.

  (* XOR r1, r2 *)
  (* XOR r2, r1 *)
  (* XOR r1, r2 *)
  do 3 basic apply *.

  (* Now we're left reasoning about XOR *)
  rewrite {2}[X in xorB w X]xorBC.
  rewrite (xorBA w w). 
  rewrite [X in xorB _ X]xorBC xorBA.
  autorewrite with bitsHints. 
  by ssimpl.
Qed.

Lemma tmpSwapCorrect s (r1 r2 rt: GPReg s) :
  |-- basicSwap r1 r2 (tmpSwapImpl r1 r2 rt) @ rt?.
Proof.
  rewrite /tmpSwapImpl/basicSwap. specintros => v w. autorewrite with push_at.
  unhideReg rt => t. 
  repeat basic apply *.
Qed.
