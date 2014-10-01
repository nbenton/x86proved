(*===========================================================================
    State transformer monad for processor
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.seq Ssreflect.eqtype Ssreflect.fintype.
Require Import x86proved.bitsops x86proved.bitsprops x86proved.monad.
Require Import x86proved.monadinst x86proved.x86.procstate x86proved.x86.exn x86proved.reader x86proved.writer x86proved.cursor x86proved.x86.ioaction x86proved.x86.addr.
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
    Register getters
  ---------------------------------------------------------------------------*)
(* Basic getter for any 64-bit register *)
Definition getReg64FromProcState r : ST QWORD :=
  let! s = getProcState;
  retn (registers s r).

(* Get an 8-bit slice of a 64-bit register *)
Definition getRegPieceFromProcState rp :=
  let: mkRegPiece r ix := rp in
  let! v = getReg64FromProcState r;
  retn (getRegPiece v ix).

(* 32-bit, 16-bit and 8-bit registers *)
Definition getReg32FromProcState (r: Reg32) := 
  let! v = getReg64FromProcState (Reg32_base r);
  retn (low 32 v). 

Definition getReg16FromProcState (r: Reg16) :=
  let! v = getReg64FromProcState (Reg16_base r);
  retn (low 16 v).

Definition getReg8FromProcState (r: Reg8) :=
  getRegPieceFromProcState (Reg8_toRegPiece r).

(*---------------------------------------------------------------------------
    Register setters
  ---------------------------------------------------------------------------*)
Definition setReg64InProcState (r:Reg64) d :=
  let! s = getProcState;
  setProcState (s!r:=d).

Definition setReg32InProcState (r: Reg32) (w: DWORD) :=
    let! v = getReg64FromProcState (Reg32_base r);
    setReg64InProcState (Reg32_base r) (updateSlice 0 32 _ v w).

Definition setReg16InProcState (r: Reg16) (w: WORD) :=
    let! v = getReg64FromProcState (Reg16_base r);
    setReg64InProcState (Reg16_base r) (updateSlice 0 16 _ v w).

Definition setReg8InProcState (r: Reg8) (w: BYTE) :=
  match r with
  | mkReg8 r64 =>
    let! v = getReg64FromProcState r64;
    setReg64InProcState r64 (updateSlice 0 8 _ v w)
  | AH => 
    let! v = getReg64FromProcState RAX;
    setReg64InProcState RAX (updateSlice 8 8 _ v w)
  | BH => 
    let! v = getReg64FromProcState RBX;
    setReg64InProcState RBX (updateSlice 8 8 _ v w)
  | CH => 
    let! v = getReg64FromProcState RCX;
    setReg64InProcState RCX (updateSlice 8 8 _ v w)
  | DH => 
    let! v = getReg64FromProcState RDX;
    setReg64InProcState RDX (updateSlice 8 8 _ v w)
  end.

Lemma setRegGetRegDistinct Y r1 v r2 (f: _ -> ST Y) s :
  ~~(r1 == r2) ->
  (do! setReg64InProcState r1 v; bind (getReg64FromProcState r2) f) s =
  (bind (getReg64FromProcState r2) (fun x => do! setReg64InProcState r1 v; f x)) s.
Proof. move => neq. rewrite /setReg64InProcState /getReg64FromProcState /=.
rewrite setThenGetDistinct; by done.
Qed.

(* Lemmas involving register lookup and update *)
Lemma doSetReg {Y} r v (f: ST Y) s :
  (do! setReg64InProcState r v; f) s = f (s !r:=v).
Proof.  rewrite /setReg64InProcState/setProcState assoc.
by rewrite EMT_bind_lift SMT_bindGet EMT_bind_lift SMT_doSet. Qed.

Lemma letGetReg {Y} (s: ProcState) r (f: QWORD -> ST Y):
  bind (getReg64FromProcState r) f s = f (registers s r) s.
Proof. rewrite /getReg64FromProcState/getProcState assoc.
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
Definition getFromProcState R {r:Reader R} (p: ADDR) : ST R :=
  let! s = getProcState;
  match readMem readNext (memory s) p with
  | readerFail => raiseExn ExnGP
  | readerWrap => raiseUnspecified
  | readerOk v _ => retn v
  end.

Definition readFromProcState R {r:Reader R} (p: ADDR) : ST (R*ADDR) :=
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

Definition setBYTEInProcState (p:ADDR) (b:BYTE)   := setInProcState p b.
Definition setWORDInProcState (p:ADDR) (d:WORD) := setInProcState p d.
Definition setDWORDInProcState (p:ADDR) (d:DWORD) := setInProcState p d.
Definition setQWORDInProcState (p:ADDR) (d:QWORD) := setInProcState p d.
Definition setVWORDInProcState {s} : ADDR -> VWORD s -> ST unit := 
  match s with
  | OpSize1 => setBYTEInProcState 
  | OpSize2 => setWORDInProcState  
  | OpSize4 => setDWORDInProcState 
  | OpSize8 => setQWORDInProcState 
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

