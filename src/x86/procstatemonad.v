(*===========================================================================
    State transformer monad for processor
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.seq Ssreflect.eqtype.
Require Import x86proved.bitsops x86proved.bitsprops x86proved.monad.
Require Import x86proved.monadinst x86proved.x86.procstate x86proved.x86.exn x86proved.reader x86proved.writer x86proved.cursor x86proved.x86.ioaction.
Require Import Coq.Strings.String Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope update_scope.

(* Output monad at bottom, wrapped with error monad, then state monad *)
Definition ST := errorMT (SMT (IOM Chan Data) ProcState) (option GeneralException).

Definition getProcState: ST ProcState := EMT_lift _ _ (SMT_get _ (S:=_)).
Definition setProcState (s: ProcState) : ST unit := EMT_lift _ _ (SMT_set _ (S:=ProcState) s).

Definition raiseUnspecified {X} : ST X := EMT_raise _ None.
Definition raiseExn {X} (e:GeneralException) : ST X := EMT_raise _ (Some e).

(*---------------------------------------------------------------------------
    Register getters and setters
  ---------------------------------------------------------------------------*)
Definition getRegFromProcState r : ST DWORD :=
  let! s = getProcState;
  retn (registers s r).

Definition getRegPieceFromProcState rp :=
  let: AnyRegPiece r ix := rp in
  let! v = getRegFromProcState r;
  retn (getRegPiece v ix).

Definition setRegInProcState (r:AnyReg) d :=
  let! s = getProcState;
  setProcState (s!r:=d).

Definition setBYTERegInProcState (r: BYTEReg) (b: BYTE) :=
  let: AnyRegPiece r ix := BYTERegToRegPiece r in
    let! d = getRegFromProcState r;
    setRegInProcState r (putRegPiece d ix b).

Definition setWORDRegInProcState (wr: WORDReg) (w: WORD) :=
    let: mkWordReg r := wr in
    let! d = getRegFromProcState r;
    setRegInProcState r (@high 16 16 d ## w).

Lemma setRegGetRegDistinct Y r1 v r2 (f: _ -> ST Y) s :
  ~~(r1 == r2) ->
  (do! setRegInProcState r1 v; bind (getRegFromProcState r2) f) s =
  (bind (getRegFromProcState r2) (fun x => do! setRegInProcState r1 v; f x)) s.
Proof. move => neq. rewrite /setRegInProcState /getRegFromProcState /=.
rewrite setThenGetDistinct; by done.
Qed.

(* Lemmas involving register lookup and update *)
Lemma doSetReg {Y} r v (f: ST Y) s :
  (do! setRegInProcState r v; f) s = f (s !r:=v).
Proof.  rewrite /setRegInProcState/setProcState assoc.
by rewrite EMT_bind_lift SMT_bindGet EMT_bind_lift SMT_doSet. Qed.

Lemma letGetReg {Y} (s: ProcState) r (f: DWORD -> ST Y):
  bind (getRegFromProcState r) f s = f (registers s r) s.
Proof. rewrite /getRegFromProcState/getProcState assoc.
by rewrite EMT_bind_lift SMT_bindGet id_l. Qed.

(*---------------------------------------------------------------------------
    Flag getters and setters
  ---------------------------------------------------------------------------*)
 
(* Retrieving a flag that is undefined leads to unspecified behaviour *)
Definition getFlagFromProcState f :=
  let! s = getProcState;
  if flags s f is mkFlag b then
    retn b
  else
    raiseUnspecified.

Definition updateFlagInProcState (f:Flag) (b:bool) :=
  let! s = getProcState;
  setProcState (s!f:=b).

Definition forgetFlagInProcState f :=
  let! s = getProcState;
  setProcState (s!f:=FlagUnspecified).

(*---------------------------------------------------------------------------
    Memory getters and setters
  ---------------------------------------------------------------------------*)

(* This is wrong because wrap-around is under-specified *)
Definition getFromProcState R {r:Reader R} (p: DWORD) : ST R :=
  let! s = getProcState;
  match readMem readNext (memory s) p with
  | readerFail => raiseExn ExnGP
  | readerWrap => raiseUnspecified
  | readerOk v _ => retn v
  end.

Definition readFromProcState R {r:Reader R} (p: DWORD) : ST (R*DWORD) :=
  let! s = getProcState;
  match readMem readNext (memory s) p with
  | readerOk v (mkCursor p) => retn (v,p)
  | _ => raiseExn ExnGP
  end.

(* See Section 5.3 in Volume 3A of Intel manuals *)
(* When effective segment limit is 0xffffffff then behaviour is unspecified for
   reads that wrap around. Otherwise, it is "correct": no partial reads or writes *)
Definition getBYTEFromProcState := getFromProcState (R:=BYTE).
Definition getWORDFromProcState := getFromProcState (R:=WORD).
Definition getDWORDFromProcState := getFromProcState (R:=DWORD).
Definition getVWORDFromProcState {s} := getFromProcState (R:=VWORD s).

Definition setInProcState {X} {W:Writer X} p (x:X) :=
  let! s = getProcState;
  match writeMem W (memory s) p x with
  | Some (p', m') =>
      setProcState (mkProcState (registers s) (flags s) m')
  | None => raiseUnspecified
  end.

Definition setBYTEInProcState (p:DWORD) (b:BYTE)   := setInProcState p b.
Definition setWORDInProcState (p:DWORD) (d:WORD) := setInProcState p d.
Definition setDWORDInProcState (p:DWORD) (d:DWORD) := setInProcState p d.
Definition setVWORDInProcState {s} : DWORD -> VWORD s -> ST unit := 
  match s with
  | OpSize1 => setBYTEInProcState 
  | OpSize2 => setWORDInProcState  
  | OpSize4 => setDWORDInProcState 
  end.

(*---------------------------------------------------------------------------
    I/O operations
  ---------------------------------------------------------------------------*)

Definition outputOnChannel (c:Chan) (d:Data) : ST unit :=
  EMT_lift _ _ (SMT_lift _ (IO_write c d)).

Definition inputOnChannel (c:Chan) : ST Data :=
  EMT_lift _ _ (SMT_lift _ (IO_read _ c)).


(*
Require Import bitsrep tuplehelp.
Instance FlagStateUpdate : Update FlagState Flag bool.
apply Build_Update.
(* Same flag *)
move => m k v w.
rewrite /update /FlagStateUpdateOps /setFlag /setBit.
induction k. simpl. rewrite beheadCons. done.
rewrite /setBitAux-/setBitAux. rewrite !theadCons!beheadCons.
rewrite IHk. simpl. done. simpl. rewrite
*)

