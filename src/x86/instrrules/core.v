(*===========================================================================
    Rules for x86 instructions in terms of [safe]
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool (* for [==] notation *) Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq (* for [catA] *) Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.bitsops.
Require Import x86proved.spec x86proved.spred x86proved.spredtotal x86proved.opred x86proved.x86.basic x86proved.x86.basicprog x86proved.spectac.
Require Import x86proved.x86.instr x86proved.pointsto x86proved.cursor.
Require Import x86proved.x86.instrsyntax.
Require Import x86proved.x86.procstatemonad (* for [ST] *) x86proved.bitsprops (* for [high_catB] *) x86proved.bitsopsprops (* for [subB_eq0] *).
Require Import x86proved.septac (* for [sdestruct] *) x86proved.obs (* for [obs] *) x86proved.triple (* for [TRIPLE] *).
Require Import x86proved.x86.eval (* for [evalInstr] *) x86proved.monad (* for [doMany] *) x86proved.monadinst (* for [Success] *).
Require Import x86proved.common_definitions (* for [eta_expand] *) x86proved.common_tactics (* for [elim_atomic_in_match'] *).
Require Import Coq.Classes.Morphisms (* for [Parametric Morphism] and [signature_scope] *).

Module Import instrruleconfig.
  Export Ssreflect.ssreflect Ssreflect.ssrbool (* for [==] notation *) Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.tuple.

  Export x86proved.x86.procstate x86proved.bitsops.
  Export x86proved.spec x86proved.spred x86proved.opred x86proved.obs x86proved.x86.basic x86proved.x86.basicprog.
  Export x86proved.x86.instr x86proved.pointsto x86proved.cursor.
  Export x86proved.x86.instrsyntax.

  Export x86proved.common_definitions (* for [eta_expand] *).

  Open Scope instr_scope.

  Global Set Implicit Arguments.
  Global Unset Strict Implicit.
End instrruleconfig.

Import Prenex Implicits.
Require Import x86proved.x86.ioaction x86proved.x86.step.

Lemma decodeAndAdvance_rule P (i j: DWORD) R sij instr O c Q :
  sij |-- i -- j :-> instr ->
  TRIPLE (P ** EIP ~= j ** sij ** R) (c instr) O (Q ** R) ->
  TRIPLE (P ** EIP ~= i ** sij ** R) (bind decodeAndAdvance c) O (Q ** R).
Proof.
move => HR T. rewrite /decodeAndAdvance.
triple_apply triple_letGetReg.
try_triple_apply triple_letReadSep. rewrite -> HR; by ssimpl.
triple_apply triple_setRegSep.
triple_apply T.
Qed.

Lemma step_rule P (i j: DWORD) R sij instr O Q :
  sij |-- i -- j :-> instr ->
  TRIPLE (EIP ~= j ** P ** sij ** R ** ltrue) (evalInstr instr) O (Q ** R ** ltrue) ->
  TRIPLE (EIP ~= i ** P ** sij ** R ** ltrue) step O (Q ** R ** ltrue).
Proof.
move => HR T. rewrite /step.
try_triple_apply decodeAndAdvance_rule. rewrite -> HR. by ssimpl.
triple_apply T.
Qed.

Section UnfoldSpec.
  Local Transparent ILPre_Ops lentails.

  Lemma TRIPLE_safe_gen (instr:Instr) P o Q (i j: DWORD) sij:
    eq_pred sij |-- i -- j :-> instr ->
    forall O',
    (forall (R: SPred),
     TRIPLE (EIP ~= j ** P ** eq_pred sij ** R) (evalInstr instr) o
            (Q ** R)) ->
    (obs O') @ Q |-- obs (catOP (eq_opred o) O') @ (EIP ~= i ** P ** eq_pred sij).
  Proof.
    move => Hsij O' HTRIPLE k R HQ. move=> s Hs.
    specialize (HTRIPLE (R**ltrue)).
    apply (step_rule Hsij) in HTRIPLE.
    apply lentails_eq in Hs.
    repeat rewrite -> sepSPA in Hs.
    apply lentails_eq in Hs.
    specialize (HTRIPLE s Hs).
    rewrite /runsForWithPrefixOf.
    destruct HTRIPLE as [sf [H1 H3]].

    apply lentails_eq in H3.
    rewrite <- sepSPA in H3.
    apply lentails_eq in H3.
    specialize (HQ _ H3).
    destruct HQ as [orest [H4 H5]].
    clear H3 Hsij.
    destruct k.
    { eexists (o ++ _).
      do ![ apply runsForWithPrefixOf0
          | eassumption
          | esplit ]. }

    (* k > 0 *)
    have LE: k <= succn k by done.
    apply (runsForWithPrefixOfLe LE) in H5.
    destruct H5 as [sf' [o'' [PRE MANY]]].
    exists (o ++ orest). rewrite /manyStep-/manyStep/oneStep.
    split. by exists o, orest.
    exists sf'. exists (o ++ o''). split; first by apply cat_preActions.
    exists sf. exists o, o''. split; first done.
    split; last done.
    intuition.
  Qed.

  Lemma TRIPLE_safeLater_gen (instr:Instr) P o Q (i j: DWORD) sij:
    eq_pred sij |-- i -- j :-> instr ->
    forall O' `{IsPointed_OPred O'},
    (forall (R: SPred),
     TRIPLE (EIP ~= j ** P ** eq_pred sij ** R) (evalInstr instr) o
            (Q ** R)) ->
    |> (obs O') @ Q |-- obs (catOP (eq_opred o) O') @ (EIP ~= i ** P ** eq_pred sij).
  Proof.
    move => Hsij O' ? HTRIPLE k R HQ. move=> s Hs.
    specialize (HTRIPLE (R**ltrue)).
    apply (step_rule Hsij) in HTRIPLE.
    apply lentails_eq in Hs.
    repeat rewrite -> sepSPA in Hs.
    apply lentails_eq in Hs.
    specialize (HTRIPLE s Hs).
    destruct HTRIPLE as [sf [H1 H3]].

    apply lentails_eq in H3.
    rewrite <- sepSPA in H3.
    apply lentails_eq in H3.
    destruct k => //.
    - destruct (_ : IsPointed_OPred O') as [o' o'H].
      exists (o ++ o'). split. by exists o, o'.
      apply runsForWithPrefixOf0.
    (* k > 0 *)
    have LT: (k < succn k)%coq_nat by done.
    have LE: k <= succn k by done.
    specialize (HQ k LT _ H3).
    destruct HQ as [orest [H4 H5]].
    clear H3 Hsij.

    destruct H5 as [sf' [o'' [PRE MANY]]]. rewrite /runsForWithPrefixOf.
    exists (o ++ orest).
    rewrite /manyStep-/manyStep/oneStep.
    split. by exists o, orest.
    exists sf'. exists (o ++ o''). split; first by apply cat_preActions.
    exists sf. exists o, o''. split; first done.
    split; last done.
    intuition.
  Qed.

End UnfoldSpec.

Lemma TRIPLE_safecatLater instr P Q (i j: DWORD) o O' `{IsPointed_OPred O'} :
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) o (Q ** R)) ->
  |-- (|> (obs O') @ Q -->> obs (catOP (eq_opred o) O') @ (EIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. rewrite /spec_reads. specintros => s Hs. autorewrite with push_at.
  rewrite sepSPA. apply limplValid.
  eapply TRIPLE_safeLater_gen; try eassumption; []. move=> R. triple_apply H.
Qed.

Lemma TRIPLE_safecat instr P Q (i j: DWORD) o O':
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) o (Q ** R)) ->
  |-- ((obs O') @ Q -->> obs (catOP (eq_opred o) O') @ (EIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. rewrite /spec_reads. specintros => s Hs. autorewrite with push_at.
  rewrite sepSPA. apply limplValid.
  eapply TRIPLE_safe_gen; [eassumption|]. move=> R. triple_apply H.
Qed.

Lemma TRIPLE_safeLater instr P Q (i j: DWORD) O `{IsPointed_OPred O}:
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) nil (Q ** R)) ->
  |-- (|> obs O @ Q -->> obs O @ (EIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. have TS:= TRIPLE_safecatLater (o:= nil).
  eforalls TS;
    repeat match goal with
             | [ |- IsPointed_OPred _ ] => eassumption
             | [ H : context[catOP (eq_opred nil) ?P] |- _ ] => rewrite -> empOPL in H
             | [ H : |-- _ |- |-- _ ] => by apply TS
             | _ => done
           end.
Qed.

Lemma TRIPLE_safe instr P Q (i j: DWORD) O :
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) nil (Q ** R)) ->
  |-- (obs O @ Q -->> obs O @ (EIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. have TS:= TRIPLE_safecat (o:= nil).
  eforalls TS. rewrite -> empOPL in TS. apply TS. done.
Qed.

Lemma TRIPLE_basic {T_OPred proj} instr P o Q:
  (forall (R: SPred), TRIPLE (P ** R) (evalInstr instr) o (Q ** R)) ->
  |-- @parameterized_basic T_OPred proj _ _ P instr (eq_opred o) Q.
Proof.
  move=> H. rewrite /parameterized_basic. specintros => i j O'.
  apply TRIPLE_safecat => R. triple_apply H.
Qed.

(*---------------------------------------------------------------------------
    Interpretations of MemSpec, RegMem, JmpTgt, used to give address-mod-generic
    presentations of rules
  ---------------------------------------------------------------------------*)

Definition interpMemSpecSrc ms (f: SPred -> DWORD -> spec) :=
    let: mkMemSpec optSIB offset := ms in
    if optSIB is Some (r, optix)
    then
      if optix is Some(rix,sc)
      then
        Forall pbase ixval addr,
        (f (regToAnyReg r ~= pbase ** regToAnyReg rix ~= ixval
                                   ** addB (addB pbase offset) (scaleBy sc ixval) :-> addr)
          addr)
      else
        Forall pbase addr,
        f (regToAnyReg r ~= pbase ** addB pbase offset :-> addr)
          addr
   else Forall addr, f (offset :-> addr) addr.

Definition interpJmpTgt (tgt: JmpTgt) (nextInstr: DWORD) (f: SPred -> DWORD -> spec) :=
  match tgt with
  | JmpTgtI t =>
    let: mkTgt offset := t in
    f empSP (addB nextInstr offset)

  | JmpTgtR r =>
    Forall addr,
    f (regToAnyReg r ~= addr) addr

  | JmpTgtM ms =>
    interpMemSpecSrc ms f
  end.

Definition specAtMemSpecDst s ms (f: (VWORD s -> SPred) -> spec) :=
    let: mkMemSpec optSIB offset := ms in
    if optSIB is Some(r,ixspec)
    then
      if ixspec is Some(rix,sc)
      then
        Forall pbase ixval,
        f (fun v => addB (addB pbase offset) (scaleBy sc ixval) :-> v)
          @ (regToAnyReg r ~= pbase ** regToAnyReg rix ~= ixval)

      else
        Forall pbase,
        f (fun v => addB pbase offset :-> v)
          @ (regToAnyReg r ~= pbase)
    else f (fun v => offset :-> v) @ empSP.

Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.

Definition specAtMemSpec s ms (f: VWORD s -> spec) :=
    let: mkMemSpec optSIB offset := ms in
    if optSIB is Some(r, ixspec)
    then
      if ixspec is Some(rix,sc)
      then
        Forall v pbase ixval,
        f v @ (regToAnyReg r ~= pbase ** regToAnyReg rix ~= ixval
               ** addB (addB pbase offset) (scaleBy sc ixval) :-> v)
      else
        Forall v pbase,
        f v @ (regToAnyReg r ~= pbase ** addB pbase offset :-> v)
    else Forall v, f v @ (offset :-> v).

Definition VRegIs s : VReg s -> VWORD s -> SPred :=
  match s as s return VReg s -> VWORD s -> SPred with
  | OpSize1 => BYTEregIs
  | OpSize2 => WORDregIs
  | OpSize4 => regIs
  end.

(** When dealing with logic, we want to reduce [stateIs] and similar to basic building blocks. *)
Hint Unfold VRegIs : finish_logic_unfolder.


Definition specAtRegMemDst s (src: RegMem s) (f: (VWORD s -> SPred) -> spec) :spec  :=
  match src with
  | RegMemR r =>
    f (fun v => VRegIs r v)

  | RegMemM ms =>
    specAtMemSpecDst ms f
  end.

Definition specAtSrc src (f: DWORD -> spec) : spec :=
  match src with
  | SrcI v =>
    f v

  | SrcR r =>
    Forall v,
    (f v @ (regToAnyReg r ~= v))

  | SrcM ms =>
    @specAtMemSpec _ ms f
  end.

Definition specAtDstSrc s (ds: DstSrc s) (f: (VWORD s -> SPred) -> VWORD s -> spec) : spec :=
  match ds with
  | DstSrcRR dst src =>
    Forall v,
    f (fun w => VRegIs dst w) v @ (VRegIs src v)

  | DstSrcRI dst src =>
    f (fun w => VRegIs dst w) src

  | DstSrcMI dst src =>
    specAtMemSpecDst dst (fun V => f V src)

  | DstSrcMR dst src =>
    Forall v,
    specAtMemSpecDst dst (fun V => f V v) @ (VRegIs src v)

  | DstSrcRM dst src =>
    specAtMemSpec src (fun v => f (fun w => VRegIs dst w) v)
  end.

Local Ltac specAt_morphism_step :=
  idtac;
  do [ progress move => *
     | hyp_setoid_rewrite -> *; reflexivity
     | progress destruct_head DstSrc
     | progress destruct_head MemSpec
     | progress destruct_head option
     | progress destruct_head prod
     | progress specintros => *
     | do !eapply lforallL
     | progress autorewrite with push_at ].

Local Ltac specAt_morphism_t :=
  rewrite /pointwise_relation => *; do !specAt_morphism_step.

Add Parametric Morphism s ms : (@specAtMemSpecDst s ms)
with signature pointwise_relation _ lentails ++> lentails
  as specAtMemSpecDst_entails_m.
Proof. rewrite /specAtMemSpecDst. specAt_morphism_t. Qed.

Add Parametric Morphism s ms : (@specAtMemSpecDst s ms)
with signature pointwise_relation _ (Basics.flip lentails) ++> Basics.flip lentails
  as specAtMemSpecDst_flip_entails_m.
Proof. rewrite /specAtMemSpecDst. specAt_morphism_t. Qed.

Add Parametric Morphism s ms : (@specAtMemSpec s ms)
with signature pointwise_relation _ lentails ++> lentails
  as specAtMemSpec_entails_m.
Proof. rewrite /specAtMemSpec. specAt_morphism_t. Qed.

Add Parametric Morphism s ms : (@specAtMemSpec s ms)
with signature pointwise_relation _ (Basics.flip lentails) ++> Basics.flip lentails
  as specAtMemSpec_flip_entails_m.
Proof. rewrite /specAtMemSpec. specAt_morphism_t. Qed.

Add Parametric Morphism s ms : (@specAtDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ lentails) ++> lentails
  as specAtDstSrc_entails_m.
Proof. rewrite /specAtDstSrc. specAt_morphism_t. Qed.

Add Parametric Morphism s ms : (@specAtDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ (Basics.flip lentails)) ++> Basics.flip lentails
  as specAtDstSrc_flip_entails_m.
Proof. rewrite /specAtDstSrc. specAt_morphism_t. Qed.

Notation "OSZCP?" := (OF? ** SF? ** ZF? ** CF? ** PF?).
Definition OSZCP o s z c p := OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p.

(** When dealing with logic, we want to reduce [stateIs] and similar to basic building blocks. *)
Hint Unfold OSZCP : finish_logic_unfolder.

(** We never want to see these when solving a goal, but they're
    convenient for statements *)
Hint Unfold makeBOP makeUOP makeMOV : instrrules_all.
Hint Unfold OSZCP scaleBy VRegIs BYTE DWORD WORD VWORD RegOrFlag_target : instrrules_side_conditions_spred.

(** These hints are global *)
(** TODO(t-jagro): Find a better place for this, or, better, generalize [InstrArg] *)
Coercion InstrArg_of_VReg s : VReg s -> InstrArg :=
match s as s return VReg s -> InstrArg with
| OpSize1 => BYTERegArg
| OpSize2 => WORDRegArg
| OpSize4 => RegArg
end.

Hint Unfold InstrArg_of_VReg : instrrules_all.

(*---------------------------------------------------------------------------
    Helpers for pieces of evaluation (adapted from spechelpers and
    triplehelpers)
  ---------------------------------------------------------------------------*)

(** Only things without [_rule]s should go in this database *)
Hint Unfold
  evalInstr
  evalSrc evalDst evalDstR evalDstM evalDstSrc evalPort
  (** Perhaps we should have [evalMov_rule] and [evalUnaryOp_rule]? *)
  evalMOV evalUnaryOp evalBinOp
  (** Maybe we should write [_rule]s for [evalShiftOp] and [evalCondition]. *)
  evalShiftOp
  makeBOP makeUOP
  (** Having to unfold [InstrArg_of_VReg] is a hack *)
  InstrArg_of_VReg
  OSZCP
  natAsDWORD
  (** Maybe we should find a better way to deal with [DWORDRegMemR], [evalShiftCount], [evalRegImm], and [SrcToRegImm] *)
  DWORDRegMemR evalShiftCount evalRegImm SrcToRegImm
  (** Maybe we should find a better way to deal with [evalJmpTgt] and [evalRegMem] *)
  evalJmpTgt evalRegMem
: instrrules_eval.

(** Originally, we had the following in a section:
<<
Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : basicapply.
Hint Rewrite
  addB0 low_catB : basicapply.

Hint Unfold interpJmpTgt : specapply.
>> *)

(** Anything with a rule gets opacified *)
Lemma evalReg_rule (r: Reg) v c O Q :
  forall S,
  TRIPLE (r~=v ** S) (c v) O Q ->
  TRIPLE (r~=v ** S) (bind (evalReg r) c) O Q.
Proof. by apply triple_letGetRegSep. Qed.
Global Opaque evalReg.

Lemma evalRegPiece_rule (rp: RegPiece) (v:BYTE) c O Q :
  forall S,
  TRIPLE (regPieceIs rp v ** S) (c v) O Q ->
  TRIPLE (regPieceIs rp v ** S) (bind (evalRegPiece rp) c) O Q.
Proof.
move => S T. rewrite /stateIs/BYTEregIs.
triple_apply triple_letGetRegPieceSep.
triple_apply T.
Qed.
Global Opaque evalRegPiece.

Lemma evalBYTEReg_rule (r: BYTEReg) (v:BYTE) c O Q :
  forall S,
  TRIPLE (r ~= v ** S) (c v) O Q ->
  TRIPLE (r ~= v ** S) (bind (evalBYTEReg r) c) O Q.
Proof. apply evalRegPiece_rule. Qed.
Global Opaque evalBYTEReg.

Lemma evalWORDReg_rule (r: WORDReg) (v:WORD) c O Q :
  forall S,
  TRIPLE (r ~= v ** S) (c v) O Q ->
  TRIPLE (r ~= v ** S) (bind (evalWORDReg r) c) O Q.
Proof.
move => S T. rewrite /stateIs/WORDregIs/WORDRegToReg/evalWORDReg. destruct r as [r].
triple_apply evalRegPiece_rule.
triple_apply evalRegPiece_rule.
replace (slice 8 8 0 v ## slice 0 8 8 v) with v.
try_triple_apply T.
rewrite /stateIs/WORDregIs/WORDRegToReg. by ssimpl.

(* @TODO: this should be in bitsprops *)
apply allBitsEq => i LT.
setoid_rewrite -> getBit_catB. rewrite /slice/split3/split2.
rewrite !getBit_high !getBit_low.
case E: (i < 8). by rewrite addn0 E.
rewrite subnK. by rewrite LT.
rewrite ltnNge. by rewrite -ltnS E.
Qed.
Global Opaque evalWORDReg.

Lemma evalVReg_rule s (r: VReg s) v c O Q :
  forall S,
  TRIPLE (VRegIs r v ** S) (c v) O Q ->
  TRIPLE (VRegIs r v ** S) (bind (evalVReg r) c) O Q.
Proof.
destruct s; [apply evalBYTEReg_rule | apply evalWORDReg_rule | apply evalReg_rule].
Qed.
Opaque evalVReg.

Lemma triple_setVRegSep s (r: VReg s) v w :
  forall S, TRIPLE (VRegIs r v ** S) (setVRegInProcState r w) nil
                   (VRegIs r w ** S).
Proof. destruct s;
  [apply triple_setBYTERegSep | apply triple_setWORDRegSep | apply triple_setRegSep]. Qed.
Global Opaque setVRegInProcState.

Lemma evalMemSpecNone_rule offset c O Q :
  forall S,
  TRIPLE S (c offset) O Q ->
  TRIPLE S (bind (evalMemSpec (mkMemSpec None offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec. triple_apply T. Qed.

Lemma evalMemSpecSomeNone_rule (r:Reg) p offset c O Q :
  forall S,
  TRIPLE (r ~= p ** S) (c (addB p offset)) O Q ->
  TRIPLE (r ~= p ** S) (bind (evalMemSpec (mkMemSpec (Some (r, None)) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec.
triple_apply triple_letGetRegSep.
triple_apply T.
Qed.

Lemma evalMemSpec_rule (r:Reg) (ix:NonSPReg) sc (p indexval offset:DWORD) c O Q :
  forall S,
  TRIPLE (r ~= p ** ix ~= indexval ** S) (c (addB (addB p offset) (scaleBy sc indexval))) O Q ->
  TRIPLE (r ~= p ** ix ~= indexval ** S) (bind (evalMemSpec (mkMemSpec (Some(r, Some (ix,sc))) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec.
triple_apply triple_letGetRegSep.
triple_apply triple_letGetRegSep.
triple_apply T.
Qed.
Global Opaque evalMemSpec.

Lemma evalPush_rule sp (v w:DWORD) (S:SPred) :
  TRIPLE (ESP~=sp ** (sp -# 4) :-> v ** S)
         (evalPush w) nil
         (ESP~=sp -# 4 ** (sp -# 4) :-> w ** S).
Proof.
rewrite/evalPush.
triple_apply triple_letGetRegSep.
triple_apply triple_setRegSep.
triple_apply triple_setDWORDSep.
Qed.
Global Opaque evalPush.

Lemma getReg_rule (r:AnyReg) v c O Q :
  forall S,
  TRIPLE (r~=v ** S) (c v) O Q ->
  TRIPLE (r~=v ** S) (bind (getRegFromProcState r) c) O Q.
Proof. by apply triple_letGetRegSep. Qed.
Global Opaque getRegFromProcState.

Lemma triple_pre_introFlags P comp O Q :
  (forall o s z c p, TRIPLE (OSZCP o s z c p ** P) comp O Q) ->
  TRIPLE (OSZCP? ** P) comp O Q.
Proof.
  rewrite /OSZCP /stateIsAny.
  (* TODO: could use an sdestruct tactic for TRIPLE. *)
  move=> H s Hs.
  sdestruct: Hs => fo Hs.
  sdestruct: Hs => fs Hs.
  sdestruct: Hs => fz Hs.
  sdestruct: Hs => fc Hs.
  sdestruct: Hs => fp Hs.
  eapply H; eassumption.
Qed.

Lemma triple_updateZPS P n (v: BITS n) z p s:
  TRIPLE (ZF ~= z ** PF ~= p ** SF ~= s ** P) (updateZPS v) nil (ZF ~= (v == #0) ** PF ~= (lsb v) ** SF ~= (msb v) ** P).
Proof. rewrite /updateZPS. move => H. do 3 triple_apply triple_setFlagSep. Qed.
Global Opaque updateZPS.

Lemma triple_letVWORDSep s (p:PTR) (v:VWORD s) c O Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) O Q ->
  TRIPLE (p:->v ** S) (bind (getVWORDFromProcState p) c) O Q.
Proof. destruct s; apply triple_letGetSep. Qed.
Global Opaque getVWORDFromProcState.

Lemma basicForgetFlags T (MI: MemIs T) P (x:T) O Q o s z c p
      (H : |-- basic (P ** OSZCP?) x O (Q ** OSZCP o s z c p))
: |-- basic P x O Q @ OSZCP?.
Proof. basic apply H. Qed.

Lemma sbbB_ZC n (r : BITS n) carry (v1 v: BITS n) :
  sbbB false v1 v = (carry, r) ->
   ZF~=(r == #(0)) ** CF~=carry |-- CF~=ltB v1 v ** ZF~=(v1 == v).
Proof. move => E.
  have S0 := subB_eq0 v1 v. rewrite E in S0. rewrite S0.
  have HH := (sbbB_ltB_leB v1 v). rewrite E/fst in HH.
  destruct carry. + rewrite HH. by ssimpl. + rewrite ltBNle HH /negb. by ssimpl.
Qed.

Section sbbB_ZC_for_rewrite.
(** TODO(t-jagro): Find a way to [setoid_rewrite] without making [sepSP] opaque here. *)
Local Opaque sepSP lentails.
Lemma sbbB_ZC' n (r : BITS n) carry (v1 v: BITS n) P Q (E : sbbB false v1 v = (carry, r))
: P ** ZF~=(r == #(0)) ** CF~=carry ** Q |-- P ** ZF~=(v1 == v) ** CF~=ltB v1 v ** Q.
Proof. sbazooka; etransitivity; try (by apply sbbB_ZC; eassumption); sbazooka. Qed.
End sbbB_ZC_for_rewrite.

Definition ConditionIs cc cv : SPred :=
  match cc with
  | CC_O => OF ~= cv
  | CC_B => CF ~= cv
  | CC_Z => ZF ~= cv
  | CC_S => SF ~= cv
  | CC_P => PF ~= cv
  | CC_BE => Exists cf zf, cv = cf || zf /\\ CF ~= cf ** ZF ~= zf
  | CC_L => Exists sf f, cv = xorb sf f /\\ SF ~= sf ** OF ~= f
  | CC_LE => Exists sf f zf, cv = (xorb sf f) || zf /\\ SF ~= sf ** OF ~= f ** ZF ~= zf
  end.

Hint Unfold ConditionIs : instrrules_side_conditions_spred.

Local Ltac triple_op_helper :=
  idtac;
  match goal with
    | [ |- TRIPLE _ (updateFlagInProcState ?f ?w_) _ _ ]      => triple_apply triple_setFlagSep
    | [ |- TRIPLE _ (updateZPS ?v) _ _ ]                      => triple_apply triple_updateZPS
    | [ |- TRIPLE _ (bind (getFlagFromProcState ?f) _) _ _ ]  => triple_apply triple_letGetFlagSep
    (** We require [?f; ?g] rather than [_; _], because [_]s can be dependent, but [triple_seq] only works in the non-dependent/constant function case *)
    | [ |- TRIPLE _ (bind ?f (fun _ : unit => ?g)) _ _ ]      => eapply triple_seq
    | _ => progress autorewrite with triple
  end.

Local Ltac triple_op_bazooka_using tac :=
  cbv zeta;
  let H := fresh in
  intro H;
    do ?tac;
    try by triple_apply H.

Local Ltac triple_op_bazooka := triple_op_bazooka_using triple_op_helper.

Lemma triple_letGetCondition cc (v:bool) P O Q c:
  TRIPLE (ConditionIs cc v ** P) (c v) O Q ->
  TRIPLE (ConditionIs cc v ** P) (bind (evalCondition cc) c) O Q.
Proof.
  rewrite /evalCondition/ConditionIs; elim cc;
  triple_op_bazooka_using ltac:(idtac;
                                match goal with
                                  | [ |- TRIPLE (lexists _ ** _) _ _ _ ]    => apply triple_pre_existsSep => ?
                                  | [ |- TRIPLE (lpropand _ _ ** _) _ _ _ ] => apply triple_pre_existsSep => ?
                                  | [ H : mkFlag _ = mkFlag _ |- _ ]      => (inversion H; try clear H)
                                  | _ => progress subst
                                  | _ => progress triple_op_helper
                                  | [ H : TRIPLE _ _ _ _ |- _ ] => triple_apply H using sbazooka
                                end).
Qed.
Global Opaque evalCondition.

Lemma evalArithUnaryOpNoCarry_rule o s z p n f arg c' O Q S
: let result := f arg in
  TRIPLE (OF ~= (msb arg != msb result) ** SF ~= msb result ** ZF ~= (result == #(0)) ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** PF ~= p ** S) (let!res = @evalArithUnaryOpNoCarry n f arg; c' res) O Q.
Proof. rewrite /evalArithUnaryOpNoCarry. triple_op_bazooka. Qed.
Global Opaque evalArithUnaryOpNoCarry.

Lemma evalArithUnaryOp_rule o s z c p n (f : BITS n -> bool * BITS n) arg c' O Q S
: let: (carry, result) := eta_expand (f arg) in
  TRIPLE (OF ~= (msb arg != msb result) ** SF ~= msb result ** ZF ~= (result == #(0)) ** CF ~= carry ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p ** S) (let!res = @evalArithUnaryOp n f arg; c' res) O Q.
Proof. rewrite /evalArithUnaryOp. triple_op_bazooka. Qed.
Global Opaque evalArithUnaryOp.

Lemma evalArithOpNoCarry_rule o s z c p n (f : bool -> BITS n -> BITS n -> bool * BITS n) arg1 arg2 c' O Q S
: let: (carry, result) := eta_expand (f false arg1 arg2) in
  TRIPLE (OF ~= computeOverflow arg1 arg2 result ** SF ~= msb result ** ZF ~= (result == #(0)) ** CF ~= carry ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p ** S) (let!res = @evalArithOpNoCarry n f arg1 arg2; c' res) O Q.
Proof. rewrite /evalArithOpNoCarry. triple_op_bazooka. Qed.
Global Opaque evalArithOpNoCarry.

(** The operation is unspecified if [CF] is unspecified. *)
Lemma evalArithOp_rule o s z (c : bool) p n (f : bool -> BITS n -> BITS n -> bool * BITS n) arg1 arg2 c' O Q S
: let: (carry, result) := eta_expand (f c arg1 arg2) in
  TRIPLE (OF ~= computeOverflow arg1 arg2 result ** SF ~= msb result ** ZF ~= (result == #(0)) ** CF ~= carry ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p ** S) (let!res = @evalArithOp n f arg1 arg2; c' res) O Q.
Proof. rewrite /evalArithOp. triple_op_bazooka. Qed.
Global Opaque evalArithOp.

Lemma evalLogicalOp_rule o s z c p n (f : BITS n -> BITS n -> BITS n) arg1 arg2 c' O Q S
: let result := f arg1 arg2 in
  TRIPLE (OF ~= false ** SF ~= msb result ** ZF ~= (result == #(0)) ** CF ~= false ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p ** S) (let!res = @evalLogicalOp n f arg1 arg2; c' res) O Q.
Proof. rewrite /evalLogicalOp. triple_op_bazooka. Qed.
Global Opaque evalLogicalOp.

Lemma evalPortI_rule (p: BYTE) c O Q S :
  TRIPLE S (c (zeroExtend 8 p)) O Q ->
  TRIPLE S (bind (evalPort p) c) O Q.
Proof. move => T. rewrite /evalPort. triple_apply T. Qed.

(** TODO(t-jagro): Find a better place for this opacity control *)
Global Opaque setRegInProcState getDWORDFromProcState updateFlagInProcState forgetFlagInProcState.

Ltac instrrule_triple_bazooka_step tac :=
  idtac;
  let tapply H := triple_apply H using tac in
  lazymatch goal with
    | [ |- TRIPLE _ (bind (@evalVReg ?s ?r) _) _ _ ]                                              => tapply (@evalVReg_rule s)
    | [ |- TRIPLE _ (bind (evalReg ?r) _) _ _ ]                                                   => tapply evalReg_rule
    | [ |- TRIPLE _ (bind (evalWORDReg ?r) _) _ _ ]                                               => tapply evalWORDReg_rule
    | [ |- TRIPLE _ (bind (evalBYTEReg ?r) _) _ _ ]                                               => tapply evalBYTEReg_rule

    | [ |- TRIPLE _ (bind (evalPort (PortI ?r)) _) _ _ ]                                          => tapply evalPortI_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec None ?offset)) _) _ _ ]                         => tapply evalMemSpecNone_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec (Some (?r, None)) ?offset)) _) _ _ ]            => tapply evalMemSpecSomeNone_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec (Some (?r, Some (?ix, ?sc))) ?offset)) _) _ _ ] => tapply evalMemSpec_rule
    | [ |- TRIPLE _ (bind (evalArithUnaryOpNoCarry ?f ?arg) _) _ _ ]                              => tapply evalArithUnaryOpNoCarry_rule
    | [ |- TRIPLE _ (bind (evalArithUnaryOp ?f ?arg) _) _ _ ]                                     => tapply evalArithUnaryOp_rule
    | [ |- TRIPLE _ (bind (evalArithOpNoCarry ?f ?arg1 ?arg2) _) _ _ ]                            => tapply evalArithOpNoCarry_rule
    | [ |- TRIPLE _ (bind (evalArithOp ?f ?arg1 ?arg2) _) _ _ ]                                   => tapply evalArithOp_rule
    | [ |- TRIPLE _ (bind (evalLogicalOp ?f ?arg1 ?arg2) _) _ _ ]                                 => tapply evalLogicalOp_rule
    | [ |- TRIPLE _ (bind (evalCondition ?cc) _) _ _ ]                                            => tapply triple_letGetCondition
    | [ |- TRIPLE _ (updateFlagInProcState ?f ?w) _ _ ]                                           => tapply triple_setFlagSep
    | [ |- TRIPLE _ (updateZPS ?v) _ _ ]                                                          => tapply triple_updateZPS
    | [ |- TRIPLE _ (forgetFlagInProcState ?f) _ _ ]                                              => do [ tapply triple_forgetFlagSep | tapply triple_forgetFlagSep' ]
    | [ |- TRIPLE _ (setRegInProcState ?d ?p) _ _ ]                                               => tapply triple_setRegSep
    | [ |- TRIPLE _ (setBYTERegInProcState ?d ?p) _ _ ]                                           => tapply triple_setBYTERegSep
    | [ |- TRIPLE _ (setVRegInProcState ?d ?p) _ _ ]                                              => tapply triple_setVRegSep
    | [ |- TRIPLE _ (setVWORDInProcState ?p ?w) _ _ ]                                             => tapply triple_setVWORDSep
    | [ |- TRIPLE _ (retn tt) _ _ ]                                                               => tapply triple_skip
    | [ |- TRIPLE _ (bind (getFlagFromProcState ?f) _) _ _ ]                                      => do [ tapply triple_letGetFlagSep | tapply triple_letGetFlag ]
    | [ |- TRIPLE _ (bind (getRegFromProcState ?r) _) _ _ ]                                       => tapply triple_letGetRegSep
    | [ |- TRIPLE _ (bind (@getVWORDFromProcState ?s ?p) _) _ _ ]                                 => tapply (@triple_letGetVWORDSep s)
    | [ |- TRIPLE _ (bind (getDWORDFromProcState ?p) _) _ _ ]                                     => tapply triple_letGetDWORDSep
    | [ |- TRIPLE _ (evalPush ?p) _ _ ]                                                           => tapply evalPush_rule
    (** We require [?f; ?g] rather than [_; _], because [_]s can be dependent, but [triple_seq] only works in the non-dependent/constant function case *)
    | [ |- TRIPLE _ (bind ?f (fun _ : unit => ?g)) _ _ ] => eapply triple_seq
    | _ => do [ apply TRIPLE_basic => *
              | triple_apply triple_pre_introFlags => *; rewrite /OSZCP
              | progress autorewrite with triple
              | progress autounfold with instrrules_eval ]
  end.

Ltac instrrule_triple_bazooka tac :=
  (try specintros => *; autorewrite with push_at);
  do !instrrule_triple_bazooka_step tac.

Tactic Notation "instrrule_triple_bazooka" "using" tactic3(tac) := instrrule_triple_bazooka tac.
Tactic Notation "instrrule_triple_bazooka" := instrrule_triple_bazooka using idtac.

Ltac change_stateIs_with_VRegIs :=
  progress repeat match goal with
                    | [ |- appcontext[stateIs (RegOrFlagDWORD (regToAnyReg ?r))] ] => progress change (stateIs r) with (@VRegIs OpSize4 r)
                  end.

(** TODO(t-jagro): Find a way to make this nicer. *)
Ltac do_instrrule_using tac :=
  do ?rewrite /specAtSrc/specAtDstSrc/specAtMemSpec/specAtMemSpecDst/specAtRegMemDst;
  try match goal with
        | [ ds : DstSrc _ |- _ ] => elim ds => ? ?
        | [ src : Src |- _ ] => elim src => ?
        | [ rm : RegMem _ |- _ ] => elim rm => ?
      end;
  do ?[ elim_atomic_in_match' | case/(@id (option _)) | case/(@id (_ * _))
        | (* ensure that the goal is of the form [_ -> _] *) (test progress intros); move => ? ];
  try by tac.
(** Make a [Tactic Notation] so we don't need [ltac:()] *)
Tactic Notation "do_instrrule" tactic3(tac) := do_instrrule_using tac.
Ltac do_instrrule_triple := do_instrrule instrrule_triple_bazooka.

(** Some convenience macros for dealing with basicapply. *)
Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : instrrules_all.
