(*===========================================================================
    Assembler for type [program]. Import this and call [assemble_program].
  ===========================================================================*)
Require Import ssreflect ssrnat ssrbool seq eqtype tuple.
Require Import tuplehelp bitsrep bitsops mem reg instr instrsyntax instrcodec cursor update.
Require Import program monad monadinst writer.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive AssemblerError := OutOfLabels | DuplicateLabel.

Definition assemblerState := seq DWORD * PMAP DWORD 32 * seq AssemblerError : Type.


(* The monad in which pass 2 does its computation. This unfolds to
   fun X => state2 -> WriterTm (state2 * X) *)
Definition ST := @SMT WriterTm assemblerState.

Definition getState: ST assemblerState := SMT_get _ (S:=_).
Definition setState: assemblerState -> ST unit := SMT_set _ (S:=_).
Coercion assemblerLift {X} (w: WriterTm X): ST X := SMT_lift _ w.

Definition getPos: ST DWORD :=
  let! pos = assemblerLift getWCursor;
  if pos is mkCursor c then retn c else writerFail.

Require Import pmap.
Fixpoint countDecLabels (p: program) : nat :=
  match p with
  | prog_seq p1 p2 => countDecLabels p1 + countDecLabels p2
  | prog_declabel body => 1 + countDecLabels (body #0)
  | _ => 0
  end.
Fixpoint countLabels (p: program) : nat :=
  match p with
  | prog_seq p1 p2 => countLabels p1 + countLabels p2
  | prog_declabel body => countLabels (body #0)
  | prog_label _ => 1
  | _ => 0
  end.

(* There is a bug with programs that define two labels at the same location *)
Fixpoint onepass (p: program) : ST unit :=
  match p with
  | prog_instr c => writeNext c
  | prog_data _ _ _ _ c => writeNext c
  | prog_skip => retn tt
  | prog_seq p1 p2 =>
      do! (onepass p1);
      onepass p2
  | prog_declabel body =>
      let! (labels, m, errors) = getState;
      if labels is addr::labels'
      then do! setState (labels', m, errors); onepass (body addr)
      else setState (labels, m, OutOfLabels::errors)
    (* In fact l will have been passed in *)
  | prog_label l =>
      let! pos = getPos;
      let! (labels, m, errors) = getState;
      setState (labels, m ! l := pos, errors)
  end.

Fixpoint finalpass (p: program) : ST unit :=
  match p with
  | prog_instr c => writeNext c
  | prog_data _ _ _ _ c => writeNext c
  | prog_skip => retn tt
  | prog_seq p1 p2 =>
      do! finalpass p1;
          finalpass p2
  | prog_declabel body =>
      let! (labels, m, errors) = getState;
      if labels is addr::labels'
      then do! setState (labels', m, errors);
           finalpass (body addr)
      else writerFail
  | prog_label l =>
      let! pos = getPos;
      if pos == l then retn tt else writerFail
  end.

Inductive AssemblerResult R :=
  AssemblerSuccess (r:R) | AssemblerFail (errors: seq AssemblerError).

Definition runOnePass (offset: DWORD) (addrs: seq DWORD) (p: program) :
  AssemblerResult (seq DWORD * seq BYTE) :=
  match runWriterTm true (onepass p (addrs,EmptyPMap _ _,nil)) offset with
  | Some ((_,m,nil,_),bytes) => AssemblerSuccess (pmap m addrs,bytes)
  | Some ((_,_,errors,_),_) => AssemblerFail _ errors
  | None => AssemblerFail _ nil
  end.

Fixpoint runNPasses n offset addrs p :=
  if n is n'.+1 then
    match runOnePass offset addrs p with
    | AssemblerSuccess (addrs', bytes)  =>
      if addrs == addrs' then AssemblerSuccess(n, addrs', bytes)
      else runNPasses n' offset addrs' p
    | AssemblerFail errors => AssemblerFail _ errors
    end
  else AssemblerFail _ nil.

Definition passes := 20.

Definition runAssembler offset p :=
  let labels := map fromNat (iota 0 (countDecLabels p)) in
  runNPasses passes offset labels p.

Instance write_program : Writer program :=
  fun p =>
    let! c = getWCursor;
    if c is mkCursor offset
    then
      if runAssembler offset p is AssemblerSuccess (_,newlabels, _)
      then
        do! finalpass p (newlabels,EmptyPMap _ _,nil); retn tt
      else writerFail
    else writerFail.

(* This is the main function of the assembler. *)
Definition assemble (offset: DWORD) (p: program) : option (seq BYTE) :=
  runWriter true write_program offset p.

(* Call this to determine whether the assembler returned something meaningful.
 *)
Definition assemble_success (offset: DWORD) (p: program) : bool :=
  match assemble offset p with
  | Some _ => true
  | None => false
  end.

Definition assembleToString offset p :=
  if assemble offset p is Some bytes then bytesToHex bytes else "ERROR"%string.
