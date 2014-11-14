(*===========================================================================
    Rules for x86 instructions in terms of [safe]
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool (* for [==] notation *) Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq (* for [catA] *) Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.bitsops.
Require Import x86proved.spec x86proved.spred x86proved.spred.spredtotal x86proved.opred x86proved.x86.basic x86proved.x86.basicprog x86proved.spectac.
Require Import x86proved.x86.instr x86proved.cursor.
Require Import x86proved.x86.instrsyntax.
Require Import x86proved.x86.procstatemonad (* for [ST] *) x86proved.bitsprops (* for [high_catB] *) x86proved.bitsopsprops (* for [subB_eq0] *).
Require Import x86proved.obs (* for [obs] *) x86proved.triple (* for [TRIPLE] *).
Require Import x86proved.x86.eval (* for [evalInstr] *) x86proved.monad (* for [doMany] *) x86proved.monadinst (* for [Success] *).
Require Import x86proved.common_definitions (* for [eta_expand] *) x86proved.common_tactics (* for [elim_atomic_in_match'] *).
Require Import Coq.Classes.Morphisms (* for [Parametric Morphism] and [signature_scope] *).

Module Import instrruleconfig.
  Export Ssreflect.ssreflect Ssreflect.ssrbool (* for [==] notation *) Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.tuple.

  Export x86proved.x86.procstate x86proved.bitsops.
  Export x86proved.spec x86proved.spred x86proved.opred x86proved.obs x86proved.x86.basic x86proved.x86.basicprog.
  Export x86proved.x86.instr x86proved.cursor.
  Export x86proved.x86.instrsyntax.

  Export x86proved.common_definitions (* for [eta_expand] *).

  Open Scope instr_scope.

  Global Set Implicit Arguments.
  Global Unset Strict Implicit.
End instrruleconfig.

Import Prenex Implicits.
Require Import x86proved.x86.ioaction x86proved.x86.step.

Lemma getReg_rule s (r: Reg s) v c O Q :
  forall S,
  TRIPLE (r ~= v ** S) (c v) O Q ->
  TRIPLE (r ~= v ** S) (bind (getRegFromProcState r) c) O Q.
Proof. Admitted.
(*destruct s; [apply evalReg8_rule | apply evalReg16_rule | apply evalReg32_rule | apply evalReg64_rule].
Qed.
Opaque evalReg.*)

Lemma triple_setRegSep s (r: Reg s) v w :
  forall S, TRIPLE (r ~= v ** S) (setRegInProcState r w) nil
                   (r ~= w ** S).
Proof. destruct s;
  [apply triple_setReg8Sep | apply triple_setReg16Sep | apply triple_setReg32Sep | apply triple_setReg64Sep]. Qed.
Global Opaque setRegInProcState.

(* Put this somewhere else *)
Lemma decodeAndAdvance_rule P (i j: ADDR) R sij instr O c Q :
  sij |-- i -- j :-> instr ->
  TRIPLE (P ** UIP ~= j ** sij ** R) (c instr) O (Q ** R) ->
  TRIPLE (P ** UIP ~= i ** sij ** R) (bind decodeAndAdvance c) O (Q ** R).
Proof.
move => HR T. rewrite /decodeAndAdvance.
triple_apply (getReg_rule (r:=UIP)). 
try_triple_apply triple_letReadSep. rewrite -> HR. by ssimpl.
triple_apply triple_setRegSep.
triple_apply T.
Qed.

Lemma step_rule P (i j: ADDR) R sij instr O Q :
  sij |-- i -- j :-> instr ->
  TRIPLE (UIP ~= j ** P ** sij ** R ** ltrue) (evalInstr instr) O (Q ** R ** ltrue) ->
  TRIPLE (UIP ~= i ** P ** sij ** R ** ltrue) step O (Q ** R ** ltrue).
Proof.
move => HR T. rewrite /step/decodeAndAdvance. 
triple_apply (getReg_rule (r:=UIP)). 
try_triple_apply triple_letReadSep. rewrite -> HR; by ssimpl.
triple_apply triple_setRegSep.
triple_apply T.
Qed.

Section UnfoldSpec.
  Local Transparent ILPre_Ops lentails.

  Lemma TRIPLE_safe_gen (instr:Instr) P o Q (i j: ADDR) sij:
    eq_pred sij |-- i -- j :-> instr ->
    forall O',
    (forall (R: SPred),
     TRIPLE (UIP ~= j ** P ** eq_pred sij ** R) (evalInstr instr) o
            (Q ** R)) ->
    (obs O') @ Q |-- obs (catOP (eq_opred o) O') @ (UIP ~= i ** P ** eq_pred sij).
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

  Lemma TRIPLE_safeLater_gen (instr:Instr) P o Q (i j: ADDR) sij:
    eq_pred sij |-- i -- j :-> instr ->
    forall O' `{IsPointed_OPred O'},
    (forall (R: SPred),
     TRIPLE (UIP ~= j ** P ** eq_pred sij ** R) (evalInstr instr) o
            (Q ** R)) ->
    |> (obs O') @ Q |-- obs (catOP (eq_opred o) O') @ (UIP ~= i ** P ** eq_pred sij).
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

Lemma TRIPLE_safecatLater instr P Q (i j: ADDR) o O' `{IsPointed_OPred O'} :
  (forall (R: SPred),
   TRIPLE (UIP ~= j ** P ** R) (evalInstr instr) o (Q ** R)) ->
  |-- (|> (obs O') @ Q -->> obs (catOP (eq_opred o) O') @ (UIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. rewrite /spec_reads. specintros => s Hs. autorewrite with push_at.
  rewrite sepSPA. apply limplValid.
  eapply TRIPLE_safeLater_gen; try eassumption; []. move=> R. triple_apply H.
Qed.

Lemma TRIPLE_safecat instr P Q (i j: ADDR) o O':
  (forall (R: SPred),
   TRIPLE (UIP ~= j ** P ** R) (evalInstr instr) o (Q ** R)) ->
  |-- ((obs O') @ Q -->> obs (catOP (eq_opred o) O') @ (UIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. rewrite /spec_reads. specintros => s Hs. autorewrite with push_at.
  rewrite sepSPA. apply limplValid.
  eapply TRIPLE_safe_gen; [eassumption|]. move=> R. triple_apply H.
Qed.

Lemma TRIPLE_safeLater instr P Q (i j: ADDR) O `{IsPointed_OPred O}:
  (forall (R: SPred),
   TRIPLE (UIP ~= j ** P ** R) (evalInstr instr) nil (Q ** R)) ->
  |-- (|> obs O @ Q -->> obs O @ (UIP ~= i ** P)) <@ (i -- j :-> instr).
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

Lemma TRIPLE_safe instr P Q (i j: ADDR) O :
  (forall (R: SPred),
   TRIPLE (UIP ~= j ** P ** R) (evalInstr instr) nil (Q ** R)) ->
  |-- (obs O @ Q -->> obs O @ (UIP ~= i ** P)) <@ (i -- j :-> instr).
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

Definition interpUIP a : Reg (adSizeToOpSize a) := match a with AdSize4 => EIP | AdSize8 => RIP end.

Definition interpMemSpecSrc s a (ms: MemSpec a) (f: SPred -> VWORD s -> spec) : spec :=
    let: mkMemSpec optSeg optSIB offset := ms in
    match optSIB with
    | Some (mkSIB r optix) =>
      if optix is Some(rix,sc)
      then
        Forall pbase ixval (addr:VWORD s),
        (f ((r:GPReg _) ~= pbase ** (rix:NonSPReg _) ~= ixval
                       ** computeIxAddr pbase offset (scaleBy sc ixval) :-> addr)
          addr)
      else
        Forall (pbase:ADR a) (v:VWORD s),
        f ((r:GPReg _) ~= pbase ** computeAddr pbase offset :-> v) v
   | Some RIPrel =>
     Forall (pbase:ADR a) (v:VWORD s),
        f (interpUIP a ~= pbase ** computeAddr pbase offset :-> v) v
   | None => 
     Forall addr:VWORD s, f (ADRtoADDR (computeDisplacement a offset) :-> addr) addr
   end.


(*@TODO: work out what coercions we need to avoid all these explicit types *)
Definition specAtMemSpecDst s a (ms:MemSpec a) (f: (VWORD s -> SPred) -> spec) :=
  match ms with
    mkMemSpec _ optSIB offset =>
    match optSIB with
    | Some (mkSIB r ixspec) =>
      if ixspec is Some(rix,sc)
      then
        Forall pbase ixval,
        f (fun v => (computeIxAddr pbase offset (scaleBy sc ixval) :-> v))
          @ ((r:GPReg _) ~= pbase ** (rix:NonSPReg _) ~= ixval)

      else
        Forall pbase,
        f (fun v => (computeAddr pbase offset) :-> v)
          @ ((r:GPReg _) ~= pbase)
 
    | Some RIPrel =>
      Forall pbase,
        f (fun v => (computeAddr pbase offset) :-> v)
          @ (interpUIP a ~= pbase)
      
    | None =>
      f (fun v => (ADRtoADDR (computeDisplacement a offset)) :-> v) @ empSP
    end
    end.

Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.

Definition specAtMemSpec s a (ms:MemSpec a) (f: VWORD s -> spec) :=
  match ms with
  | mkMemSpec _ optSIB offset =>
    match optSIB with
    | Some(mkSIB r ixspec) =>
      if ixspec is Some(rix,sc)
      then
        Forall v pbase ixval,
        f v @ ((r:GPReg _) ~= pbase ** (rix:NonSPReg _) ~= ixval
               ** computeIxAddr pbase offset (scaleBy sc ixval) :-> v)
      else
        Forall v pbase,
        f v @ ((r:GPReg _) ~= pbase ** computeAddr pbase offset :-> v)
    | Some RIPrel =>
        Forall v pbase,
        f v @ (interpUIP a ~= pbase ** computeAddr pbase offset :-> v)

    | None => 
      Forall v, f v @ (ADRtoADDR (computeDisplacement a offset) :-> v)
    end
    end.

Definition specAtRegMemDst s (src: RegMem s) (f: (VWORD s -> SPred) -> spec) :spec  :=
  match src with
  | RegMemR r =>
    f (fun v => r ~= v)

  | RegMemM a ms =>
    specAtMemSpecDst ms f
  end.

Definition interpJmpTgt (tgt: JmpTgt AdSize8) (nextInstr: ADDR) (f: SPred -> ADDR -> spec) :=
  match tgt with
  | JmpTgtI t =>
    let: mkTgt d := t in
    f empSP (addB nextInstr d)

  | JmpTgtRegMem (RegMemR r) =>
    Forall addr:ADDR,
    f (r ~= addr) addr

  | JmpTgtRegMem (RegMemM a ms) =>
    interpMemSpecSrc (s:=OpSize8) ms f
  end.

Definition specAtSrc src (f: QWORD -> spec) : spec :=
  match src with
  | SrcI v =>
    f (signExtend _ v)

  | SrcR r =>
    Forall v,
    f v @ (r ~= v)

  | SrcM a ms =>
    specAtMemSpec ms f
  end.

Definition specAtDstSrc s (ds: DstSrc s) (f: (VWORD s -> SPred) -> VWORD s -> spec) : spec :=
  match ds with
  | DstSrcRR dst src =>
    Forall v,
    f (fun w => dst ~= w) v @ (src ~= v)

  | DstSrcRI dst src =>
    f (fun w => dst ~= w) (getImm src)

  | DstSrcMI a dst src =>
    specAtMemSpecDst dst (fun V => f V (getImm src))

  | DstSrcMR a dst src =>
    Forall v,
    specAtMemSpecDst dst (fun V => f V v) @ (src ~= v)

  | DstSrcRM a dst src =>
    specAtMemSpec src (fun v => f (fun w => dst ~= w) v)
  end.

Definition specAtMovDstSrc s (ds: MovDstSrc s) (f: (VWORD s -> SPred) -> VWORD s -> spec) : spec :=
  match ds with
  | MovDstSrcRR dst src =>
    Forall v,
    f (fun w => dst ~= w) v @ (src ~= v)

  | MovDstSrcRI dst src =>
    f (fun w => dst ~= w) src

  | MovDstSrcMI a dst src =>
    specAtMemSpecDst dst (fun V => f V (getImm src))

  | MovDstSrcMR a dst src =>
    Forall v,
    specAtMemSpecDst dst (fun V => f V v) @ (src ~= v)

  | MovDstSrcRM a dst src =>
    specAtMemSpec src (fun v => f (fun w => dst ~= w) v)
  end.

Local Ltac specAt_morphism_step :=
  idtac;
  do [ progress move => *
     | hyp_setoid_rewrite -> *; reflexivity
     | progress destruct_head DstSrc
     | progress destruct_head MovDstSrc
     | progress destruct_head SIB
     | progress destruct_head MemSpec
     | progress destruct_head option
     | progress destruct_head prod
     | progress specintros => *
     | do !eapply lforallL
     | progress autorewrite with push_at ].

Local Ltac specAt_morphism_t :=
  rewrite /pointwise_relation => *; do !specAt_morphism_step.

Add Parametric Morphism a s ms : (@specAtMemSpecDst a s ms)
with signature pointwise_relation _ lentails ++> lentails
  as specAtMemSpecDst_entails_m.
Proof. rewrite /specAtMemSpecDst. specAt_morphism_t => //. Qed.

Add Parametric Morphism a s ms : (@specAtMemSpecDst a s ms)
with signature pointwise_relation _ (Basics.flip lentails) ++> Basics.flip lentails
  as specAtMemSpecDst_flip_entails_m.
Proof. rewrite /specAtMemSpecDst. specAt_morphism_t => //. Qed.

Add Parametric Morphism a s ms : (@specAtMemSpec a s ms)
with signature pointwise_relation _ lentails ++> lentails
  as specAtMemSpec_entails_m.
Proof. rewrite /specAtMemSpec. specAt_morphism_t => //. Qed.

Add Parametric Morphism a s ms : (@specAtMemSpec a s ms)
with signature pointwise_relation _ (Basics.flip lentails) ++> Basics.flip lentails
  as specAtMemSpec_flip_entails_m.
Proof. rewrite /specAtMemSpec. specAt_morphism_t => //. Qed.

Add Parametric Morphism s ms : (@specAtDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ lentails) ++> lentails
  as specAtDstSrc_entails_m.
Proof. rewrite /specAtDstSrc. specAt_morphism_t. Qed.

Add Parametric Morphism s ms : (@specAtDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ (Basics.flip lentails)) ++> Basics.flip lentails
  as specAtDstSrc_flip_entails_m.
Proof. rewrite /specAtDstSrc. specAt_morphism_t. Qed.

Add Parametric Morphism s ms : (@specAtMovDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ lentails) ++> lentails
  as specAtMovDstSrc_entails_m.
Proof. rewrite /specAtMovDstSrc. specAt_morphism_t. Qed.

Add Parametric Morphism s ms : (@specAtMovDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ (Basics.flip lentails)) ++> Basics.flip lentails
  as specAtMovDstSrc_flip_entails_m.
Proof. rewrite /specAtMovDstSrc. specAt_morphism_t. Qed.

Notation "OSZCP?" := (OF? ** SF? ** ZF? ** CF? ** PF?).
Definition OSZCP o s z c p := OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p.

(** When dealing with logic, we want to reduce [stateIs] and similar to basic building blocks. *)
Hint Unfold OSZCP : finish_logic_unfolder.

(** We never want to see these when solving a goal, but they're
    convenient for statements *)
Hint Unfold makeBOP makeMOV makeUOP makeLEA VWORDasIMM : instrrules_all.
Hint Unfold OSZCP scaleBy BYTE DWORD WORD VWORD RegOrFlag_target : instrrules_side_conditions_spred.

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
  evalShiftOp evalPop
  makeBOP makeUOP makeLEA VWORDasIMM
  OSZCP
  natAsDWORD
  (** Maybe we should find a better way to deal with [evalShiftCount], [evalRegImm], and [SrcToRegImm] *)
  evalShiftCount evalRegImm (*SrcToRegImm*)
  (** Maybe we should find a better way to deal with [evalJmpTgt] and [evalRegMem] *)
  evalJmpAdr evalJmpAddr evalRegMem getImm
  computeDisplacement adSizeToOpSize computeAddr computeIxAddr getUIP setUIP
  setAdrRegInProcState
: instrrules_eval.

(** Anything with a rule gets opacified *)
Lemma evalRegPiece_rule (rp: RegPiece) (v:BYTE) c O Q :
  forall S,
  TRIPLE (regPieceIs rp v ** S) (c v) O Q ->
  TRIPLE (regPieceIs rp v ** S) (bind (getRegPieceFromProcState rp) c) O Q.
Proof.
move => S T. 
triple_apply triple_letGetRegPieceSep.
triple_apply T.
Qed.

Lemma evalMemSpecDisp_rule a seg (offset:DWORD) c O Q :
  forall S,
  TRIPLE S (c (ADRtoADDR (computeDisplacement a offset))) O Q ->
  TRIPLE S (bind (evalMemSpec (mkMemSpec a seg None offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec. destruct a; destruct seg => //. Qed.

Lemma evalMemSpecAdrDisp_rule a seg (offset:DWORD) c O Q :
  forall S,
  TRIPLE S (c (computeDisplacement a offset)) O Q ->
  TRIPLE S (bind (evalMemSpecAdr (mkMemSpec a seg None offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec. destruct a; destruct seg => //. Qed. 

Lemma evalMemSpecBase_rule a seg (r:BaseReg a) p (offset:DWORD) c O Q :
  forall S,
  TRIPLE ((r:GPReg _) ~= p ** S) (c (computeAddr p offset)) O Q ->
  TRIPLE ((r:GPReg _) ~= p ** S) (bind (evalMemSpec (mkMemSpec a seg (Some (mkSIB a r None)) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec/evalMemSpecAdr.
destruct a; destruct seg => //;
  triple_apply getReg_rule;
  triple_apply T.
Qed.

Lemma evalMemSpecAdrBase_rule a seg (r:BaseReg a) p (offset:DWORD) c O Q :
  forall S,
  TRIPLE ((r:GPReg _) ~= p ** S) (c (computeAdr p offset)) O Q ->
  TRIPLE ((r:GPReg _) ~= p ** S) (bind (evalMemSpecAdr (mkMemSpec a seg (Some (mkSIB a r None)) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec/evalMemSpecAdr.
destruct a; 
destruct seg;
  triple_apply getReg_rule;
  triple_apply T.
Qed.

Lemma evalMemSpecRIPrel_rule a seg p (offset:DWORD) c O Q :
  forall S,
  TRIPLE (interpUIP a ~= p ** S) (c (computeAddr p offset)) O Q ->
  TRIPLE (interpUIP a ~= p ** S) (bind (evalMemSpec (mkMemSpec a seg (Some (RIPrel _)) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec/evalMemSpecAdr.
destruct a; destruct seg; 
  triple_apply getReg_rule;
  triple_apply T.
Qed.

Lemma evalMemSpecAdrRIPrel_rule a seg p (offset:DWORD) c O Q :
  forall S,
  TRIPLE (interpUIP a ~= p ** S) (c (computeAdr p offset)) O Q ->
  TRIPLE (interpUIP a ~= p ** S) (bind (evalMemSpecAdr (mkMemSpec a seg (Some (RIPrel _)) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpecAdr.
destruct a; destruct seg; 
  triple_apply getReg_rule;
  triple_apply T.
Qed.

Lemma evalMemSpecAdrSIB_rule a seg (r:BaseReg a) (ix:IxReg a) sc (p indexval:ADR a) (offset:DWORD) c O Q :
  forall S,
  TRIPLE ((r:GPReg _) ~= p ** (ix:NonSPReg _) ~= indexval ** S) (c (computeIxAdr p offset (scaleBy sc indexval))) O Q ->
  TRIPLE ((r:GPReg _) ~= p ** (ix:NonSPReg _) ~= indexval ** S) (bind (evalMemSpecAdr (mkMemSpec a seg (Some (mkSIB _ r (Some (ix,sc)))) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpecAdr.
destruct a; 
  destruct seg;
  triple_apply getReg_rule;
  triple_apply getReg_rule;
  triple_apply T. 
Qed.

Lemma evalMemSpecSIB_rule a seg (r:BaseReg a) (ix:IxReg a) sc (p indexval:ADR a) (offset:DWORD) c O Q :
  forall S,
  TRIPLE ((r:GPReg _) ~= p ** (ix:NonSPReg _) ~= indexval ** S) (c (computeIxAddr p offset (scaleBy sc indexval))) O Q ->
  TRIPLE ((r:GPReg _) ~= p ** (ix:NonSPReg _) ~= indexval ** S) (bind (evalMemSpec (mkMemSpec a seg (Some (mkSIB _ r (Some (ix,sc)))) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec/evalMemSpecAdr/evalSegBase.
destruct a; destruct seg;
  triple_apply getReg_rule;
  triple_apply getReg_rule;
  triple_apply T. 
Qed.
Global Opaque evalMemSpec.

Hint Unfold opSizeToNat computeDisplacement computeAddr computeIxAddr interpUIP : ssimpl. 

Lemma evalPush_rule (sp:QWORD) (v w:QWORD) (S:SPred) :
  TRIPLE (USP~=sp ** (sp -# 8) :-> v ** S)
         (evalPush w) nil
         (USP~=sp -# 8 ** (sp -# 8) :-> w ** S).
Proof.
rewrite/evalPush.
triple_apply (getReg_rule (s:=OpSize8)).
triple_apply triple_setRegSep.
triple_apply triple_setSep.
Qed.
Global Opaque evalPush.

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
Proof. rewrite /updateZPS. move => H. do 3 triple_apply triple_setFlagSep.
Qed.
Global Opaque updateZPS.

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
  TRIPLE S (c (zeroExtend _ p)) O Q ->
  TRIPLE S (bind (evalPort p) c) O Q.
Proof. move => T. rewrite /evalPort. triple_apply T. Qed.

(** TODO(t-jagro): Find a better place for this opacity control *)
Global Opaque getFromProcState updateFlagInProcState forgetFlagInProcState.

Ltac instrrule_triple_bazooka_step tac :=
  idtac;
  let tapply H := triple_apply H using tac in
  lazymatch goal with
  (* Get from registers and flags *)
    | [ |- TRIPLE _ (bind (getFlagFromProcState ?f) _) _ _ ]  => do [ tapply triple_letGetFlagSep | tapply triple_letGetFlag ]
    | [ |- TRIPLE _ (bind (@getRegFromProcState ?s ?r) _) _ _ ]    => tapply (@getReg_rule s r)

  (* Various derived notions *)
    | [ |- TRIPLE _ (bind (evalPort (PortI ?r)) _) _ _ ]                   => tapply evalPortI_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec _ _ None ?offset)) _) _ _ ]  => tapply evalMemSpecDisp_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec _ _ (Some (@mkSIB _ ?r None)) ?offset)) _) _ _ ] => tapply evalMemSpecBase_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec _ _ (Some (@RIPrel _)) ?offset)) _) _ _ ] => tapply evalMemSpecRIPrel_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec _ _ (Some (@mkSIB _ ?r (Some (?ix, ?sc)))) ?offset)) _) _ _ ] => tapply evalMemSpecSIB_rule
    | [ |- TRIPLE _ (bind (evalMemSpecAdr (mkMemSpec _ _ None ?offset)) _) _ _ ]  => tapply evalMemSpecAdrDisp_rule
    | [ |- TRIPLE _ (bind (evalMemSpecAdr (mkMemSpec _ _ (Some (@mkSIB _ ?r None)) ?offset)) _) _ _ ] => tapply evalMemSpecAdrBase_rule
    | [ |- TRIPLE _ (bind (evalMemSpecAdr (mkMemSpec _ _ (Some (@RIPrel _)) ?offset)) _) _ _ ] => tapply evalMemSpecAdrRIPrel_rule
    | [ |- TRIPLE _ (bind (evalMemSpecAdr (mkMemSpec _ _ (Some (@mkSIB _ ?r (Some (?ix, ?sc)))) ?offset)) _) _ _ ] => tapply evalMemSpecAdrSIB_rule
    | [ |- TRIPLE _ (bind (evalArithUnaryOpNoCarry ?f ?arg) _) _ _ ]       => tapply evalArithUnaryOpNoCarry_rule
    | [ |- TRIPLE _ (bind (evalArithUnaryOp ?f ?arg) _) _ _ ]              => tapply evalArithUnaryOp_rule
    | [ |- TRIPLE _ (bind (evalArithOpNoCarry ?f ?arg1 ?arg2) _) _ _ ]     => tapply evalArithOpNoCarry_rule
    | [ |- TRIPLE _ (bind (evalArithOp ?f ?arg1 ?arg2) _) _ _ ]            => tapply evalArithOp_rule
    | [ |- TRIPLE _ (bind (evalLogicalOp ?f ?arg1 ?arg2) _) _ _ ]          => tapply evalLogicalOp_rule
    | [ |- TRIPLE _ (bind (evalCondition ?cc) _) _ _ ]                     => tapply triple_letGetCondition
    | [ |- TRIPLE _ (updateFlagInProcState ?f ?w) _ _ ]                    => tapply triple_setFlagSep
    | [ |- TRIPLE _ (updateZPS ?v) _ _ ]                                   => tapply triple_updateZPS
    | [ |- TRIPLE _ (forgetFlagInProcState ?f) _ _ ]                       => do [ tapply triple_forgetFlagSep | tapply triple_forgetFlagSep' ]

   (* Set registers *)
    | [ |- TRIPLE _ (setRegInProcState ?d ?p) _ _ ]                       => tapply triple_setRegSep

   (* Set memory *)
    | [ |- TRIPLE _ (@setInProcState ?W (@writer.writeVWORD ?s) ?p ?w) _ _ ]       => tapply (@triple_setVWORDSep s)
    | [ |- TRIPLE _ (@setInProcState ?W ?writer ?p ?w) _ _ ]               => tapply (@triple_setSep W _ writer)

    | [ |- TRIPLE _ (retn tt) _ _ ]                                        => tapply triple_skip
    | [ |- TRIPLE _ (bind (@getFromProcState ?R ?reader ?p) _) _ _ ]       => tapply (@triple_letGetSep R reader)
    | [ |- TRIPLE _ (evalPush ?p) _ _ ]                                  => tapply evalPush_rule
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

(** TODO(t-jagro): Find a way to make this nicer. *)
Ltac do_instrrule_using tac :=
  do ?rewrite /specAtSrc/specAtDstSrc/specAtMovDstSrc/specAtMemSpec/specAtMemSpecDst/specAtRegMemDst;
  try match goal with
        | [ ds : DstSrc _ |- _ ] => elim ds => ? ?
        | [ src : Src |- _ ] => elim src => ?
        | [ rm : RegMem _ |- _ ] => elim rm => ?
        | [ a : AdSize |- _ ] => elim a
        | [ s : SIB _ |- _ ] => elim s
      end;
  do ?[ elim_atomic_in_match' | case/(@id (option _)) | case/(@id (_ * _))
        | (* ensure that the goal is of the form [_ -> _] *) (test progress intros); move => ? ];
  try by tac.
(** Make a [Tactic Notation] so we don't need [ltac:()] *)
Tactic Notation "do_instrrule" tactic3(tac) := do_instrrule_using tac.
Ltac do_instrrule_triple := do_instrrule instrrule_triple_bazooka.

(** Some convenience macros for dealing with basicapply. *)
Hint Unfold
  specAtDstSrc specAtMovDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  natAsDWORD getImm
  : instrrules_all.
