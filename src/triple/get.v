Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.procstatemonad (* for [getRegFromProcState] *).
Require Import x86proved.spred (* for [:->] *) x86proved.cursor (* for [ADDR >-> DWORDCursor] *).
Require Import x86proved.common_tactics.

Require Import x86proved.triple.morphisms.
Require Import x86proved.triple.get_readable.
Require Import x86proved.triple.monad.

Import Prenex Implicits.

(** * Get registers *)

Local Transparent ILFun_Ops SABIOps PStateSepAlgOps.

Local Ltac pre_let :=
  let lem := match goal with
               | [ |- valued_TRIPLE ?v' ?P' _ ?O2 ?P'' -> valued_TRIPLE ?v' ?P0 (bind ?c1 ?c2) ?O0 ?P'' ]
                 => constr:(fun O1 v => @valued_triple_seqcat _ _ P0 P' P'' O1 O2 c1 c2 v v' O0)
             end in
  eapply lem; first by apply cat0s.

(** In order to get [specialize_all_ways] to pick up values to
    [specialize] hypotheses with, such as [Registers] or [Flags],
    we'll have to [pose] them before we start. *)

Local Ltac get_t :=
  do 5?[ do ![ move => ?
             | progress hnf in *
             | progress rewrite -> eq_refl in *
             | congruence
             | progress destruct_head_hnf and
             | progress destruct_head_hnf ex
             | progress destruct_head_hnf or
             | hyp_apply *; congruence
             | progress simpl in * ]
       | specialize_all_ways ].

Lemma getRegPieceSep (r : Reg64) ix v (P : SPred) (s : ProcState)
: P |-- regPieceIs (mkRegPiece r ix) v ** ltrue -> P s -> v = getRegPiece (registers s r) ix.
Proof.
  pose Registers.
  pose (mkRegPiece r ix).
  move => H pre.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  apply Some_inj.
  symmetry.
  get_t.
Qed.

Lemma triple_letGetRegPiece rp (v:BYTE) (P Q:SPred) O c:
  (P |-- regPieceIs rp v  ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getRegPieceFromProcState rp) c) O Q.
Proof. move => ?. pre_let. triple_by_compute. apply: getRegPieceSep; eassumption. Qed.

Local Transparent sepLogicOps sepSP ltrue lexists lentails land.

Lemma getFlagSep (fl : Flag) (v : bool) (P : SPred) (s : ProcState)
: P |-- fl ~= v ** ltrue -> P s -> v = flags s fl :> FlagVal.
Proof. pose Flags. get_t. Qed.

Lemma triple_letGetFlag (fl:Flag) (v:bool) (P Q: SPred) O c:
  (P |-- fl ~= v ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getFlagFromProcState fl) c) O Q.
Proof.
  move => ?. pre_let. triple_by_compute; trivial.
  erewrite <- getFlagSep by eassumption.
  triple_post_compute; by do !split.
Qed.


(** * Get registers *)

Lemma triple_letGetRegPieceSep rp v c O Q :
 forall S,
 TRIPLE (regPieceIs rp v ** S) (c v) O Q ->
 TRIPLE (regPieceIs rp v ** S) (bind (getRegPieceFromProcState rp) c) O Q.
Proof. move => S T. apply: triple_letGetRegPiece. cancel2. reflexivity. done. Qed.

Lemma regPieceSep r P (s: ProcState) b i : (regPieceIs (mkRegPiece r i) b ** P) s ->
  getRegPiece (registers s r) i = b.
Proof. move => [s1 [s2 [Hs [Hs1 Hs2]]]].
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Registers (mkRegPiece r i) b).
  rewrite /= in Hs. injection Hs => //. by rewrite -Hs1/= eq_refl.
Qed.

Lemma getRegSep (r : Reg OpSize8) v (P : SPred) (s : ProcState)
: P |-- r ~= v ** ltrue -> P s -> v = registers s r.
Proof.
  move => H pre.
  rewrite /stateIs/reg64Is in H.
  have H0 := H. rewrite ->sepSPA in H0. have R0 := regPieceSep (H0 _ pre). clear H0.

  have H1 := H. rewrite <-sepSPA in H1. rewrite -> (sepSPC (regPieceIs (mkRegPiece r 0) _)) in H1.
  do 3 rewrite ->sepSPA in H1. have R1 := regPieceSep (H1 _ pre).

  have H2 := H1. rewrite <-sepSPA in H2. rewrite -> (sepSPC (regPieceIs (mkRegPiece r 2) _)) in H2.   
  do 2 rewrite <-sepSPA in H2. rewrite <- sepSPC in H2. have R2 := regPieceSep (H2 _ pre).
  clear H2.

  have H3 := H1. do 2 rewrite <-sepSPA in H3.  rewrite -> sepSPC in H3. do 2 rewrite ->sepSPA in H3.
  have R3 := regPieceSep (H3 _ pre). clear H3.

  have H3 := H1. do 3 rewrite <-sepSPA in H3.  rewrite -> sepSPC in H3. do 2 rewrite <-sepSPA in H3.
  rewrite -> sepSPC in H3. rewrite ->sepSPA in H3. have R4 := regPieceSep (H3 _ pre). clear H3.
  have H3 := H1. do 4 rewrite <-sepSPA in H3.  rewrite -> sepSPC in H3. do 2 rewrite <-sepSPA in H3.
  rewrite -> sepSPC in H3. rewrite ->sepSPA in H3. have R5 := regPieceSep (H3 _ pre). clear H3.
  have H3 := H1. do 5 rewrite <-sepSPA in H3.  rewrite -> sepSPC in H3. do 2 rewrite <-sepSPA in H3.
  rewrite -> sepSPC in H3. rewrite ->sepSPA in H3. have R6 := regPieceSep (H3 _ pre). clear H3.
  have H3 := H1. do 6 rewrite <-sepSPA in H3.  rewrite -> sepSPC in H3. do 2 rewrite <-sepSPA in H3.
  rewrite -> sepSPC in H3. rewrite ->sepSPA in H3. have R7 := regPieceSep (H3 _ pre). clear H3.
  have H3 := H1. do 2 rewrite <-sepSPA in H3.  rewrite -> sepSPC in H3. do 2 rewrite <-sepSPA in H3.
  rewrite -> sepSPC in H3. rewrite ->sepSPA in H3. have R8 := regPieceSep (H3 _ pre). clear H3.
  clear H. 
  apply getRegPiece_ext. 
  case; first done. 
  case; first done. 
  case; first done. 
  case; first done. 
  case; first done. 
  case; first done. 
  case; first done. 
  case; first done. 
  done.  
Qed.

Lemma getSegRegSep (r : SegReg) (w : WORD) (P : SPred) (s : ProcState)
: P |-- r ~= w ** ltrue -> P s -> w = segregisters s r.
Proof. 
  pose SegRegisters.
  move => H pre.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  apply Some_inj.
  symmetry.
  get_t.
Qed. 

Lemma triple_letGetSegReg (r:SegReg) (w:WORD) (P Q: SPred) O c:
  (P |-- r ~= w ** ltrue) ->
  TRIPLE P (c w) O Q ->
  TRIPLE P (bind (getSegRegFromProcState r) c) O Q.
Proof.
  move => ?. pre_let. triple_by_compute; trivial.
  erewrite <- getSegRegSep by eassumption.
  done.  
Qed.


Lemma triple_letGetReg64 (r:Reg OpSize8) v (P Q:SPred) O c:
  (P |-- r ~= v ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getReg64FromProcState r) c) O Q.
Proof. move => ?. pre_let. triple_by_compute. apply: getRegSep; eassumption. Qed.

Lemma triple_letGetReg64Sep (r:Reg OpSize8) v c O Q :
 forall S,
 TRIPLE (r~=v ** S) (c v) O Q ->
 TRIPLE (r~=v ** S) (bind (getReg64FromProcState r) c) O Q.
Proof. move => S T. apply: triple_letGetReg64. cancel2. reflexivity. done. Qed.

Lemma triple_letGetReg32 (r:Reg OpSize4) v (P Q:SPred) O c:
  (P |-- r ~= v ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getReg32FromProcState r) c) O Q.
Proof. move => H. pre_let. triple_by_compute.
rewrite /stateIs/reg32Is in H. repeat rewrite -> sepSPA in H. admit.  Qed.

Lemma triple_letGetReg8 (r:Reg OpSize1) v (P Q:SPred) O c:
  (P |-- r ~= v ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getReg8FromProcState r) c) O Q.
Proof. move => H. pre_let. triple_by_compute.
rewrite /stateIs/reg8Is in H. elim E:(Reg8_toRegPiece r) => * //. rewrite E in H. clear E. 
split => //.
apply: getRegPieceSep => //. by rewrite <- H. 
Qed. 

Lemma triple_letGetReg16 (r:Reg OpSize2) v (P Q:SPred) O c:
  (P |-- r ~= v ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getReg16FromProcState r) c) O Q.
Proof. move => H. pre_let. triple_by_compute.
rewrite /stateIs/reg16Is in H. admit. 
Qed. 

Lemma triple_letGetReg32Sep (r:Reg OpSize4) v c O Q :
 forall S,
 TRIPLE (r~=v ** S) (c v) O Q ->
 TRIPLE (r~=v ** S) (bind (getReg32FromProcState r) c) O Q.
Proof. move => S T. apply: triple_letGetReg32. cancel2. reflexivity. done. Qed.

Lemma triple_letGetFlagSep (fl:Flag) (v:bool) c O Q :
  forall S,
  TRIPLE (fl~=v ** S) (c v) O Q ->
  TRIPLE (fl~=v ** S) (bind (getFlagFromProcState fl) c) O Q.
Proof. move => S T. apply: triple_letGetFlag. cancel2. reflexivity. done. Qed.

Lemma triple_letGetSegRegSep (r:SegReg) (v:WORD) c O Q :
  forall S,
  TRIPLE (r~=v ** S) (c v) O Q ->
  TRIPLE (r~=v ** S) (bind (getSegRegFromProcState r) c) O Q.
Proof. move => S T. apply: triple_letGetSegReg. cancel2. reflexivity. done. Qed.

Lemma triple_doGetReg64 (r:Reg OpSize8) (P Q: SPred) O c :
  TRIPLE P c O Q ->
  TRIPLE P (do! getReg64FromProcState r; c) O Q.
Proof. move => T s pre. move: (T s pre) => [f [eq H']]. eexists f.
simpl. by destruct (c s). Qed.

Lemma triple_doGetFlag (f:Flag) (v:bool) (Q: SPred) O c :
  forall S,
  TRIPLE (f~=v ** S) c O Q ->
  TRIPLE (f~=v ** S) (do! getFlagFromProcState f; c) O Q.
Proof. apply (triple_letGetFlagSep (c:=fun _ => c)). Qed.

(** Get DWORDs from memory *)
(*
Lemma triple_letGetDWORDSep a (p:ADR a) (v:DWORD) c O Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) O Q ->
  TRIPLE (p:->v ** S) (bind (getDWORDFromProcState p) c) O Q.
Proof. apply triple_letGetSep. Qed.

Lemma triple_letGetQWORDSep a (p:ADR a) (v:QWORD) c O Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) O Q ->
  TRIPLE (p:->v ** S) (bind (getQWORDFromProcState p) c) O Q.
Proof. apply triple_letGetSep. Qed.

Lemma triple_letGetVWORDSep {s} a (p:ADR a) (v:VWORD s) c O Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) O Q ->
  TRIPLE (p:->v ** S) (bind (getVWORDFromProcState p) c) O Q.
Proof. destruct s; apply triple_letGetSep. Qed.
*)