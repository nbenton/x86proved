Ltac type_of t := type of t (* ssreflect bug workaround *).
(*===========================================================================
    Rules for x86 instructions in terms of [safe]
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval step monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

(* TODO: needed now? *)
Lemma TRIPLE_nopost P (c: ST unit):
  TRIPLE (P ** ltrue) c ltrue ->
  forall s: ProcState, (P ** ltrue) s -> 
    exists s', exists o, c s = (o, Success _ (s', tt)).
Proof.
  move=> HTRIPLE s Hs. move/(_ s Hs): HTRIPLE => [s' [o [Hs' _]]].
  by exists s', o.
Qed.

Section UnfoldSpec.
  Transparent ILPre_Ops.

  Lemma TRIPLE_safe_gen (instr:Instr) P Q (i j: DWORD) sij:
    eq_pred sij |-- i -- j :-> instr ->
    (forall (R: SPred),
     TRIPLE (EIP ~= j ** P ** eq_pred sij ** R) (evalInstr instr)
            (Q ** R)) ->
    |> safe @ Q |-- safe @ (EIP ~= i ** P ** eq_pred sij).
  Proof.
    move => Hsij HTRIPLE k R HQ. move=> s Hs.
    destruct k; first apply runsFor0. (* everything's safe in 0 steps *)
    rewrite /runsFor. 

    move: s Hs. apply: TRIPLE_nopost. rewrite /doMany-/doMany.
    rewrite assoc. triple_apply triple_letGetRegSep. 
    rewrite assoc. triple_apply triple_letReadSep. rewrite ->Hsij. by ssimpl.
    rewrite assoc. eapply triple_seq. triple_apply triple_setRegSepGen. by ssimpl.
    eapply triple_seq. triple_apply HTRIPLE.

    move=> s Hs.
    edestruct (HQ k) as [f [o Hf]] => //. 
    - rewrite ->lentails_eq. rewrite ->sepSPA, <-lentails_eq.
      eassumption.
    exists f. exists o. by split.
  Qed.
End UnfoldSpec.

Lemma TRIPLE_safe instr P Q (i j: DWORD):
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) (Q ** R)) ->
  |-- (|> safe @ Q -->> safe @ (EIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. rewrite /spec_reads. specintros => s Hs. autorewrite with push_at.
  rewrite sepSPA. apply limplValid.
  eapply TRIPLE_safe_gen; [eassumption|]. move=> R. triple_apply H.
Qed.

Lemma TRIPLE_basic instr P Q:
  (forall (R: SPred), TRIPLE (P ** R) (evalInstr instr) (Q ** R)) ->
  |-- basic P instr Q.
Proof.
  move=> H. rewrite /basic. specintros => i j.
  rewrite ->(spec_later_weaken (safe @ (EIP~=j ** Q))).
  apply TRIPLE_safe => R. triple_apply H.
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

Definition specAtMemSpecDst dword ms (f: (DWORDorBYTE dword -> SPred) -> spec) :=
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

(*
Definition lentails1 {T} (f g:T -> SPred):= forall x , f x |-- g x.
Definition lentails2 {T} (f g: (T -> SPred) -> spec) := forall x y, lentails1 x y ->
lentails (f x) (f y).
Global Instance specAtMemSpecDst_entails_m dword :
    Proper (eq --> lentails2 --> lentails) (@specAtMemSpecDst dword).
Proof.
  move => ms1 ms2 msE.
  rewrite /Basics.flip in msE. subst.
  move => f1 f2 fE.
  rewrite /Basics.flip/lentails2 in fE.
  rewrite /specAtMemSpecDst.
  destruct ms1.
  destruct sib.
  destruct p.
  destruct o.
  destruct p.
  specintros => pbase1 ixval1.
  rewrite /lentails1 in fE.
  specsplit.
  autorewrite with push_at.
  sbazooka. ssimpl.
  simpl. specintros.
  autorewrite with push_at. specintros => pbase2 ixval2.
  simpl. g fg.
  move => P P' HP c _ <- Q Q' HQ. apply: basic_roc; try eassumption.
    done.
  Qed.
*)

Definition specAtMemSpec dword ms (f: DWORDorBYTE dword -> spec) :=
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

Definition BYTEregIsAux (r: BYTEReg) (d:DWORD) (b: BYTE) : SPred :=
  match r in BYTEReg return SPred with
  | AL => low 8 d == b /\\ EAX ~= d
  | BL => low 8 d == b /\\ EBX ~= d
  | CL => low 8 d == b /\\ ECX ~= d
  | DL => low 8 d == b /\\ EDX ~= d
  | AH => low 8 (@high 24 8 d) == b /\\ EAX ~= d
  | BH => low 8 (@high 24 8 d) == b /\\ EBX ~= d
  | CH => low 8 (@high 24 8 d) == b /\\ ECX ~= d
  | DH => low 8 (@high 24 8 d) == b /\\ EDX ~= d
  end.

Definition BYTEregIs r b := Exists d, BYTEregIsAux r d b.

Definition DWORDorBYTEregIs d : DWORDorBYTEReg d -> DWORDorBYTE d -> SPred :=
  if d as d return DWORDorBYTEReg d -> DWORDorBYTE d -> SPred
  then fun r v => r ~= v else fun r v => BYTEregIs r v.


Definition specAtRegMemDst d (src: RegMem d) (f: (DWORDorBYTE d -> SPred) -> spec) :spec  :=
  match src with
  | RegMemR r =>
    f (fun v => DWORDorBYTEregIs r v)

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
    @specAtMemSpec true ms f
  end.

Definition specAtDstSrc dword (ds: DstSrc dword) (f: (DWORDorBYTE dword -> SPred) -> DWORDorBYTE dword -> spec) : spec :=
  match ds with
  | DstSrcRR dst src =>
    Forall v,
    f (fun w => DWORDorBYTEregIs dst w) v @ (DWORDorBYTEregIs src v)

  | DstSrcRI dst src =>
    f (fun w => DWORDorBYTEregIs dst w) src

  | DstSrcMI dst src =>
    specAtMemSpecDst dst (fun V => f V src)

  | DstSrcMR dst src =>
    Forall v,
    specAtMemSpecDst dst (fun V => f V v) @ (DWORDorBYTEregIs src v)

  | DstSrcRM dst src =>
    specAtMemSpec src (fun v => f (fun w => DWORDorBYTEregIs dst w) v)
  end.

Notation "OSZCP?" := (OF? ** SF? ** ZF? ** CF? ** PF?).
Definition OSZCP o s z c p := OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p.

(* We open a section in order to localize the hints *)
Section InstrRules.

Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : basicapply.
Hint Rewrite
  addB0 low_catB : basicapply.

(*---------------------------------------------------------------------------
    Helpers for pieces of evaluation (adapted from spechelpers and
    triplehelpers)
  ---------------------------------------------------------------------------*)

Hint Unfold
  evalInstr
  evalArithOp evalArithOpNoCarry evalArithUnaryOp evalArithUnaryOpNoCarry
  evalLogicalOp evalBinOp evalShiftOp evalUnaryOp evalCondition
  evalMOV evalDst evalDstR evalDstM evalSrc evalMemSpec evalBYTEReg : eval.


Lemma evalReg_rule (r: Reg) v c Q :
  forall S,
  TRIPLE (r~=v ** S) (c v) Q ->
  TRIPLE (r~=v ** S) (bind (evalReg r) c) Q.
Proof. by apply triple_letGetRegSep. Qed.

(* Is there a  better way of doing this? *)
Lemma triple_preEq (T: eqType) (v w:T) P c Q :
  TRIPLE (v == w /\\ P) (c w) Q ->
  TRIPLE (v == w /\\ P) (c v) Q.
Proof. move => S. apply: triple_pre_exists => H. rewrite -(eqP H) eq_refl in S.
triple_apply S; sbazooka. Qed.

Lemma evalBYTERegAux_rule (r: BYTEReg) d v c Q :
  forall S,
  TRIPLE (BYTEregIsAux r d v ** S) (c v) Q ->
  TRIPLE (BYTEregIsAux r d v ** S) (bind (evalBYTEReg r) c) Q.
Proof.
rewrite /evalBYTEReg/BYTEregIsAux.
move => S T.
destruct r; triple_apply triple_letGetReg; sbazooka.
+ triple_apply (@triple_preEq _ (low 8 d) v (EAX~=d ** S)); sbazooka.
  triple_apply T; sbazooka.
+ triple_apply (@triple_preEq _ (low 8 d) v (EBX~=d ** S)); sbazooka.
  triple_apply T; sbazooka.
+ triple_apply (@triple_preEq _ (low 8 d) v (ECX~=d ** S)); sbazooka.
  triple_apply T; sbazooka.
+ triple_apply (@triple_preEq _ (low 8 d) v (EDX~=d ** S)); sbazooka.
  triple_apply T; sbazooka.
+ triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (EAX~=d ** S)); sbazooka.
  triple_apply T; sbazooka.
+ triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (EBX~=d ** S)); sbazooka.
  triple_apply T; sbazooka.
+ triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (ECX~=d ** S)); sbazooka.
  triple_apply T; sbazooka.
+ triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (EDX~=d ** S)); sbazooka.
  triple_apply T; sbazooka.
Qed.

Lemma evalBYTEReg_rule (r: BYTEReg) v c Q :
  forall S,
  TRIPLE (BYTEregIs r v ** S) (c v) Q ->
  TRIPLE (BYTEregIs r v ** S) (bind (evalBYTEReg r) c) Q.
Proof.
move => S T.
apply triple_pre_existsSep => d.
triple_apply evalBYTERegAux_rule. rewrite /BYTEregIs in T.
triple_apply T; sbazooka.
Qed.

Lemma evalDWORDorBYTEReg_rule d(r: DWORDorBYTEReg d) v c Q :
  forall S,
  TRIPLE (DWORDorBYTEregIs r v ** S) (c v) Q ->
  TRIPLE (DWORDorBYTEregIs r v ** S) (bind (evalDWORDorBYTEReg _ r) c) Q.
Proof.
destruct d; [apply evalReg_rule | apply evalBYTEReg_rule].
Qed.

Lemma ASSOC (D: WORD) (b c:BYTE) : (D ## b) ## c = D ## b ## c.
Proof. rewrite /catB. apply val_inj. simpl. by rewrite -catA. Qed.

Lemma LOWLEMMA (D: WORD) (b c:BYTE): low 8 (@high 24 8 (D ## b ## c)) == b.
Proof. by rewrite -ASSOC high_catB low_catB. Qed.

Lemma triple_setBYTERegSep r v w :
  forall S, TRIPLE (BYTEregIs r v ** S) (setBYTERegInProcState r w) (BYTEregIs r w ** S).
Proof.
move => S.
rewrite /BYTEregIsAux/setBYTERegInProcState.
destruct r; apply triple_pre_existsSep => d; apply triple_pre_existsSep => _;
  triple_apply triple_letGetRegSep; triple_apply triple_setRegSep.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.
Qed.

Lemma triple_doSetDWORDSep (p:PTR) (v w: DWORD) c Q S :
  TRIPLE (p:->w ** S) c Q ->  
  TRIPLE (p:->v ** S) (do! setDWORDInProcState p w; c) Q.
Proof. move => T s pre. 
destruct (triple_setDWORDSep w pre) as [f [o [H1 H2]]]. 
specialize (T _ H2). 
destruct T as [f' [o' H3]]. exists f'. rewrite /= H1.
eexists _.  
destruct (c f). destruct H3.  split; last done. by injection H => -> ->. 
Qed. 

Lemma triple_doSetBYTESep (p:PTR) (v w: BYTE) c Q S :
  TRIPLE (p:->w ** S) c Q ->  
  TRIPLE (p:->v ** S) (do! setBYTEInProcState p w; c) Q.
Proof. move => T s pre. 
destruct (triple_setBYTESep w pre) as [f [o [H1 H2]]]. 
specialize (T _ H2). 
destruct T as [f' [o' H3]]. exists f'. rewrite /= H1.
eexists _.  
destruct (c f). destruct H3.  split; last done. by injection H => -> ->. 
Qed. 

Lemma triple_doSetBYTERegSep (r:BYTEReg) (v w:BYTE) c Q :
  forall S, 
  TRIPLE (BYTEregIs r w ** S) c Q ->  
  TRIPLE (BYTEregIs r v ** S) (do! setBYTERegInProcState r w; c) Q.
Proof. move => S. 
eapply triple_seq. apply triple_setBYTERegSep. Qed. 


Lemma triple_setDWORDorBYTERegSep d (r: DWORDorBYTEReg d) v w :
  forall S, TRIPLE (DWORDorBYTEregIs r v ** S) (setDWORDorBYTERegInProcState _ r w)
                   (DWORDorBYTEregIs r w ** S).
Proof. destruct d; [apply triple_setRegSep | apply triple_setBYTERegSep]. Qed.

Lemma evalMemSpecNone_rule (r:Reg) p offset c Q :
  forall S,
  TRIPLE (r ~= p ** S) (c (addB p offset)) Q ->
  TRIPLE (r ~= p ** S) (bind (evalMemSpec (mkMemSpec (Some (r, None)) offset)) c) Q.
Proof. move => S T. rewrite /evalMemSpec.
triple_apply triple_letGetRegSep.
triple_apply T.
Qed.

Lemma evalMemSpec_rule (r:Reg) (ix:NonSPReg) sc p indexval offset c Q :
  forall S,
  TRIPLE (r ~= p ** ix ~= indexval ** S) (c (addB (addB p offset) (scaleBy sc indexval))) Q ->
  TRIPLE (r ~= p ** ix ~= indexval ** S) (bind (evalMemSpec (mkMemSpec (Some(r, Some (ix,sc))) offset)) c) Q.
Proof. move => S T. rewrite /evalMemSpec.
triple_apply triple_letGetRegSep.
triple_apply triple_letGetRegSep; sbazooka.
triple_apply T.
Qed.

Lemma evalPush_rule sp (v w:DWORD) (S:SPred) :
  TRIPLE (ESP~=sp ** (sp -# 4) :-> v ** S)
         (evalPush w)
         (ESP~=sp -# 4 ** (sp -# 4) :-> w ** S).
Proof.
triple_apply triple_letGetRegSep.
triple_apply triple_doSetRegSep.
triple_apply triple_setDWORDSep.
Qed.

Lemma getReg_rule (r:AnyReg) v c Q :
  forall S,
  TRIPLE (r~=v ** S) (c v) Q ->
  TRIPLE (r~=v ** S) (bind (getRegFromProcState r) c) Q.
Proof. by apply triple_letGetRegSep. Qed.

Lemma triple_pre_introFlags P comp Q :
  (forall o s z c p, TRIPLE (OSZCP o s z c p ** P) comp Q) ->
  TRIPLE (OSZCP? ** P) comp Q.
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

Lemma triple_doUpdateZPS P Q n (v: BITS n) c z p s:
  TRIPLE (ZF ~= (v == #0) ** PF ~= (lsb v) ** SF ~= (msb v) ** P) c Q ->
  TRIPLE (ZF ~= z ** PF ~= p ** SF ~= s ** P) (do!updateZPS v; c) Q.
Proof.
  move=> H. rewrite /updateZPS.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply H.
Qed.

(*---------------------------------------------------------------------------
    PUSH instruction
  ---------------------------------------------------------------------------*)

(* Generic rule *)
Lemma PUSH_rule src sp (v:DWORD) :
  |-- specAtSrc src (fun w =>
      basic    (ESP ~= sp    ** sp-#4 :-> v) (PUSH src)
               (ESP ~= sp-#4 ** sp-#4 :-> w)).
Proof.
rewrite /specAtSrc. destruct src.
- apply TRIPLE_basic => R. repeat autounfold with eval.
  triple_apply evalPush_rule.
- rewrite /specAtMemSpec.
  elim: ms => [optSIB offset].
  case: optSIB => [[base indexAndScale] |].
  case: indexAndScale => [[rix sc] |].
  + specintros => oldv pbase indexval.
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply evalPush_rule.
  + specintros => oldv pbase.
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply evalPush_rule.
  + specintros => oldv.
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc/evalMemSpec.
    triple_apply triple_letGetDWORDSep.
    triple_apply evalPush_rule.

- specintros => oldv.
  autorewrite with push_at.
  apply TRIPLE_basic => R.
  rewrite /evalInstr.
  triple_apply triple_letGetRegSep.
  triple_apply evalPush_rule.
Qed.

Ltac basicPUSH :=
  match goal with
  | |- |-- basic ?p (PUSH ?a) ?q => basicapply (PUSH_rule a)
  end.

(* PUSH r *)
Corollary PUSH_R_rule (r:Reg) sp (v w:DWORD) :
  |-- basic (r ~= v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH r)
            (r ~= v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(* PUSH v *)
Corollary PUSH_I_rule (sp v w:DWORD) :
  |-- basic (ESP ~= sp    ** sp-#4 :-> w)
            (PUSH v)
            (ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(* PUSH [r + offset] *)
Corollary PUSH_M_rule (r: Reg) (offset:nat) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH [r + offset])
            (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(* PUSH [r] *)
Corollary PUSH_M0_rule (r: Reg) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH [r])
            (r ~= pbase ** pbase :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(*---------------------------------------------------------------------------
    POP instruction
  ---------------------------------------------------------------------------*)

(* Generic POP *)
Lemma POP_rule (rm:RegMem true) (sp:DWORD) (oldv v:DWORD):
  |-- specAtRegMemDst rm (fun V =>
      basic (V oldv ** ESP ~= sp    ** sp:->v) (POP rm)
            (V v    ** ESP ~= sp+#4 ** sp:->v)).
Proof.
  rewrite /specAtRegMemDst. destruct rm.
  + apply TRIPLE_basic => R.
    repeat autounfold with eval. rewrite /DWORDorBYTEregIs.
    triple_apply evalReg_rule.
    triple_apply evalReg_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetRegSep.
    triple_apply triple_setRegSep.
  + rewrite /specAtMemSpecDst.
    elim: ms => [optSIB offset].
    elim: optSIB => [[base indexAndScale] |].
    case: indexAndScale => [[rix sc] |].
    - specintros => pbase indexval.
      autorewrite with push_at. apply TRIPLE_basic => R.
      rewrite /evalInstr.
      triple_apply evalReg_rule.
      rewrite /evalDst/evalDstM.
      triple_apply evalMemSpec_rule.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_doSetDWORDSep.
      triple_apply triple_setRegSep.
    - specintros => pbase.
      autorewrite with push_at. apply TRIPLE_basic => R.
      rewrite /evalInstr/evalDst/evalDstM.
      triple_apply evalReg_rule.
      triple_apply evalMemSpecNone_rule.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_doSetDWORDSep.
      triple_apply triple_setRegSep.
    - autorewrite with push_at.
      apply TRIPLE_basic => R.
      rewrite /evalInstr/evalDst/evalDstM.
      triple_apply evalReg_rule.
      rewrite /evalMemSpec.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_doSetDWORDSep.
      triple_apply triple_setRegSep.
Qed.

Ltac basicPOP :=
  match goal with
  | |- |-- basic ?p (POP ?a) ?q => basicapply (POP_rule a)
  end.


(* POP r *)
Corollary POP_R_rule (r:Reg) (sp oldv v:DWORD) :
  |-- basic (r ~= oldv ** ESP ~= sp    ** sp:->v) (POP (RegMemR true r))
            (r ~= v    ** ESP ~= sp+#4 ** sp:->v).
Proof. basicPOP. Qed.

(* POP [r + offset] *)
Corollary POP_M_rule (r:Reg) (offset:nat) (sp oldv v pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> oldv ** ESP ~= sp ** sp :-> v)
            (POP [r + offset])
            (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp+#4 ** sp :-> v).
Proof. basicPOP. Qed.

(* POP [r] *)
Corollary POP_M0_rule (r: Reg) (sp oldv v pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> oldv ** ESP ~= sp    ** sp :-> v)
            (POP [r])
            (r ~= pbase ** pbase :-> v    ** ESP ~= sp+#4 ** sp :-> v).
Proof. basicPOP. Qed.

(*---------------------------------------------------------------------------
    MOV instruction
  ---------------------------------------------------------------------------*)

Lemma triple_letGetDWORDorBYTESep d (p:PTR) (v:DWORDorBYTE d) c Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) Q ->
  TRIPLE (p:->v ** S) (bind (getDWORDorBYTEFromProcState _ p) c) Q.
Proof. destruct d; [apply triple_letGetSep | apply triple_letGetBYTESep]. Qed.

(* Generic rule *)
Lemma MOV_rule d ds oldv:
  |-- specAtDstSrc ds (fun V v =>
      basic (V oldv) (MOVOP d ds) (V v)).
Proof.
rewrite /specAtDstSrc.
destruct ds.

+ specintros => v. autorewrite with push_at. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply triple_setDWORDorBYTERegSep.

+ rewrite /specAtMemSpec.
  elim: src => [optSIB offset].
  case: optSIB => [[base indexopt] |].
  case: indexopt => [[ixreg sc] |].
  - specintros => v pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalMOV.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_setDWORDorBYTERegSep.
  - specintros => v pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalMOV.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_setDWORDorBYTERegSep.
  - specintros => v. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalMOV/evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_setDWORDorBYTERegSep.

+ rewrite /specAtMemSpecDst.
  specintros => v.
  elim: dst => [optSIB offset].
  elim: optSIB => [[base indexopt] |].
  case: indexopt => [[ixreg sc] |].
  - autorewrite with push_at. specintros => pbase ixval.
    autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalMOV.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply evalMemSpec_rule.
    triple_apply triple_setDWORDorBYTESep.
  - specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalMOV.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_setDWORDorBYTESep.
  - autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalMOV/evalMemSpec.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_setDWORDorBYTESep.

+ apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV.
  triple_apply triple_setDWORDorBYTERegSep.

+ rewrite /specAtMemSpecDst.
  elim: dst => [optSIB offset].
  elim: optSIB => [[base indexopt] |].
  case: indexopt => [[ixreg sc] |].
  - specintros => pbase ixval.
    autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalMOV.
    triple_apply evalMemSpec_rule.
    triple_apply triple_setDWORDorBYTESep.
  - specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalMOV.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_setDWORDorBYTESep.
  - autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalMOV/evalMemSpec.
    triple_apply triple_setDWORDorBYTESep.
Qed.

Ltac basicMOV :=
  try unfold makeMOV;
  match goal with
  | |- |-- basic ?p (@MOVOP ?d ?a) ?q => basicapply (@MOV_rule d a)
  end.

(* Register to register *)
Lemma MOV_RR_rule (r1 r2:Reg) v1 v2:
  |-- basic (r1 ~= v1 ** r2 ~= v2) (MOV r1, r2) (r1 ~= v2 ** r2 ~= v2).
Proof. basicMOV. Qed.

Lemma MOV_RanyR_rule (r1 r2:Reg) v2:
  |-- basic (r1? ** r2 ~= v2) (MOV r1, r2) (r1 ~= v2 ** r2 ~= v2).
Proof. unhideReg r1 => old. basicMOV. Qed.

(* Immediate to register *)
Lemma MOV_RI_rule (r:Reg) (v1 v2:DWORD) :
  |-- basic (r ~= v1) (MOV r, v2) (r ~= v2).
Proof. basicMOV. Qed.

Lemma MOV_RanyI_rule (r:Reg) (v2:DWORD) :
  |-- basic r? (MOV r, v2) (r ~= v2).
Proof. unhideReg r => old. basicMOV. Qed.

(* Memory to register *)
Lemma MOV_RM_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2: DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2)
            (MOV r1, [r2 + offset])
            (r1 ~= v2 ** r2 ~= pd ** pd +# offset :-> v2).
Proof. basicMOV. Qed.

Lemma MOV_RanyM_rule (pd:DWORD) (r1 r2:Reg) offset (v2: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd +# offset :-> v2)
            (MOV r1, [r2 + offset])
            (r1 ~= v2 ** r2 ~= pd ** pd +# offset :-> v2).
Proof. unhideReg r1 => old. basicMOV. Qed.

Lemma MOV_RM0_rule (pd:DWORD) (r1 r2:Reg) (v1 v2: DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd :-> v2)
            (MOV r1, [r2])
            (r1 ~= v2 ** r2 ~= pd ** pd :-> v2).
Proof. basicMOV. Qed.

Lemma MOV_RanyM0_rule (pd:DWORD) (r1 r2:Reg) (v2: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd :-> v2)
            (MOV r1, [r2])
            (r1 ~= v2 ** r2 ~= pd ** pd :-> v2).
Proof. unhideReg r1 => old. basicMOV. Qed.

(* Register to memory *)
Lemma MOV_MR_rule (p: DWORD) (r1 r2: Reg) offset (v1 v2:DWORD) :
  |-- basic (r1~=p ** p +# offset :-> v1 ** r2~=v2)
            (MOV [r1 + offset], r2)
            (r1~=p ** p +# offset :-> v2 ** r2~=v2).
Proof. basicMOV. Qed.

(* Immediate to memory *)
Lemma MOV_MI_rule dword (pd:DWORD) (r:Reg) offset (v w:DWORDorBYTE dword) :
  |-- basic (r ~= pd ** pd +# offset :-> v)
            (MOVOP _ (DstSrcMI dword (mkMemSpec (Some(r, None)) #offset) w))
            (r ~= pd ** pd +# offset :-> w).
Proof. basicMOV. Qed.

Lemma MOV_M0R_rule (pd:DWORD) (r1 r2:Reg) (v1 v2: DWORD) :
  |-- basic (r1 ~= pd ** pd :-> v1 ** r2 ~= v2)
            (MOV [r1], r2)
            (r1 ~= pd ** pd :-> v2 ** r2 ~= v2).
Proof. basicMOV. Qed.


Lemma MOV_MbR_rule (p: DWORD) (r1:Reg) (r2: BYTEReg) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** BYTEregIs r2 v2)
            (MOV [r1 + offset], r2)
            (r1 ~= p ** p +# offset :-> v2 ** BYTEregIs r2 v2).
Proof. basicMOV. Qed.

Lemma MOV_MbR_ruleGen d (p: DWORD) (r1:Reg) (r2: DWORDorBYTEReg d) offset (v1 v2:DWORDorBYTE d):
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** DWORDorBYTEregIs r2 v2)
            (MOVOP d (DstSrcMR d (mkMemSpec (Some(r1,None)) #offset) r2))
            (r1 ~= p ** p +# offset :-> v2 ** DWORDorBYTEregIs r2 v2).
Proof.
  destruct d.
  apply MOV_MR_rule.
  apply MOV_MbR_rule.
Qed.

Lemma MOV_RMb_rule (p: DWORD) (r1:Reg) (r2:BYTEReg) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** BYTEregIs r2 v2)
            (MOV r2, [r1 + offset])
            (r1 ~= p ** p +# offset :-> v1 ** BYTEregIs r2 v1).
Proof. basicMOV. Qed.

Lemma MOV_MbI_rule (pd:DWORD) (r1:Reg) offset (v1 v2:BYTE) :
  |-- basic (r1 ~= pd ** pd +# offset :-> v1)
            (MOV BYTE [r1 + offset], v2)
            (r1 ~= pd ** pd +# offset :-> v2).
Proof. basicMOV. Qed.

(*---------------------------------------------------------------------------
    LEA instruction
  ---------------------------------------------------------------------------*)

Lemma LEA_ruleSameBase (v indexval offset: DWORD) (r: Reg) (r1:NonSPReg) sc :
  |-- basic (r ~= v ** r1 ~= indexval)
            (instr.LEA r (RegMemM _ (mkMemSpec (Some(r, Some(r1, sc))) offset)))
            (r ~= addB (addB v offset) (scaleBy sc indexval) ** r1 ~= indexval).
Proof.
  apply TRIPLE_basic => R. rewrite /evalInstr.
  triple_apply evalMemSpec_rule.
  triple_apply triple_setRegSep.
Qed.

Lemma LEA_rule (old v indexval offset: DWORD) (r r': Reg) (r1:NonSPReg) sc :
  |-- basic (r ~= old ** r' ~= v ** r1 ~= indexval)
            (instr.LEA r (RegMemM _ (mkMemSpec (Some(r', Some(r1, sc))) offset)))
            (r ~= addB (addB v offset) (scaleBy sc indexval) ** r' ~= v ** r1 ~= indexval).
Proof.
  apply TRIPLE_basic => R. rewrite /evalInstr.
  triple_apply evalMemSpec_rule.
  triple_apply triple_setRegSep.
Qed.

(*---------------------------------------------------------------------------
    Unary operations
  ---------------------------------------------------------------------------*)

(* Generic increment/decrement rule *)
Lemma INCDEC_rule d (dir: bool) (src:RegMem d) oldv o s z c pf:
  |-- specAtRegMemDst src (fun V =>
      basic (V oldv ** OSZCP o s z c pf) (if dir then UOP d OP_INC src else UOP d OP_DEC src)
      (let w := if dir then incB oldv else decB oldv in
      V w ** OSZCP (msb oldv!=msb w) (msb w) (w == #0) c (lsb w))).
Proof.
rewrite /specAtRegMemDst.
destruct src.
  apply TRIPLE_basic => R.
  autounfold with eval. rewrite /evalDst/evalDstR.
  destruct dir;
    triple_apply evalDWORDorBYTEReg_rule; rewrite /evalUnaryOp/OSZCP/evalArithUnaryOpNoCarry;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep.

destruct ms.
+ elim sib => [[r indexAndScale] |].
  destruct indexAndScale. destruct p as [rix sc]. rewrite /specAtMemSpecDst.
  specintros => pbase ixval.
  autorewrite with push_at.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstM.
  destruct dir.
  - triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp.
    rewrite /evalArithUnaryOpNoCarry/OSZCP.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.
  - triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.

rewrite /specAtMemSpecDst.
specintros => pbase.
autorewrite with push_at.  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstM/evalSrc.
  destruct dir.
  - triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.
  - triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.

rewrite /specAtMemSpecDst.
autorewrite with push_at.  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstM/evalMemSpec.
    rewrite /evalSrc.
  destruct dir.
  - triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.
  - triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.
Qed.

Definition INC_rule := Eval hnf in @INCDEC_rule true true.
Definition DEC_rule := Eval hnf in @INCDEC_rule true false.

Ltac basicINCDEC :=
  try unfold makeUOP;
  match goal with
  | |- |-- basic ?p (@UOP ?d OP_INC ?a) ?q => basicapply (@INCDEC_rule d true a)
  | |- |-- basic ?p (@UOP ?d OP_DEC ?a) ?q => basicapply (@INCDEC_rule d false a)
  end.

(* Special case for increment register *)
Corollary INC_R_rule (r:Reg) (v:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (INC r)
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Corollary INC_M_rule (r:Reg) (offset:nat) (v pbase:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** OSZCP o s z c pf) (INC [r + offset])
            (r ~= pbase ** pbase +# offset :-> w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Lemma basicForgetFlags T (MI: MemIs T) P (x:T) Q o s z c p:
  |-- basic (P ** OSZCP?) x (Q ** OSZCP o s z c p) ->
  |-- basic P x Q @ OSZCP?.
Proof. move => H. autorewrite with push_at.
basicapply H. rewrite /OSZCP/stateIsAny. sbazooka.
Qed.

Lemma INC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (INC r) (r~=incB v) @ OSZCP?.
Proof.
autorewrite with push_at. rewrite /stateIsAny. specintros => o s z c p.
basicINCDEC; rewrite /OSZCP/stateIsAny; sbazooka.
Qed.

(* Special case for decrement *)
Lemma DEC_R_rule (r:Reg) (v:DWORD) o s z c pf :
  let w := decB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (DEC r)
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Lemma DEC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (DEC r) (r~=decB v) @ OSZCP?.
Proof.
autorewrite with push_at. rewrite /stateIsAny. specintros => o s z c p.
basicINCDEC; rewrite /OSZCP/stateIsAny; sbazooka.
Qed.


Lemma NOT_rule d (src:RegMem d) v:
  |-- specAtRegMemDst src (fun V => basic (V v) (UOP d OP_NOT src) (V (invB v))).
Proof.
rewrite /specAtRegMemDst.
destruct src.
  apply TRIPLE_basic => R.
  repeat autounfold with eval.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply triple_setDWORDorBYTERegSep.

rewrite /specAtMemSpecDst.
destruct ms.
case sib => [[r indexAndScale] |].
destruct indexAndScale.
destruct p as [rix sc].
specintros => pbase ixval.
autorewrite with push_at. apply TRIPLE_basic => R.
  autounfold with eval.
  rewrite /evalDst/evalDstM/evalInstr/evalUnaryOp.
  triple_apply evalMemSpec_rule.
  triple_apply triple_letGetDWORDorBYTESep.
  triple_apply triple_setDWORDorBYTESep.

specintros => pbase.
autorewrite with push_at. apply TRIPLE_basic => R.
  autounfold with eval.
  rewrite /evalDst/evalDstM/evalSrc/evalUnaryOp.
  triple_apply evalMemSpecNone_rule.
  triple_apply triple_letGetDWORDorBYTESep.
  triple_apply triple_setDWORDorBYTESep.

autorewrite with push_at. apply TRIPLE_basic => R.
  autounfold with eval.
  rewrite /evalDst/evalDstM/evalSrc/evalUnaryOp. rewrite /evalMemSpec.
  triple_apply triple_letGetDWORDorBYTESep.
  triple_apply triple_setDWORDorBYTESep.
Qed.

Ltac basicNOT :=
  try unfold makeUOP;
  match goal with
  | |- |-- basic ?p (@UOP ?d OP_NOT ?a) ?q => basicapply (@NOT_rule d a)
  end.


(* Special case for not *)
Lemma NOT_R_rule (r:Reg) (v:DWORD):
  |-- basic (r~=v) (NOT r) (r~=invB v).
Proof. basicNOT. Qed.

Corollary NOT_M_rule (r:Reg) (offset:nat) (v pbase:DWORD):
  |-- basic (r~=pbase ** pbase +# offset :-> v) (NOT [r + offset])
            (r~=pbase ** pbase +# offset :-> invB v).
Proof. basicNOT. Qed.

(* Special case for negation *)
Lemma NEG_R_rule (r:Reg) (v:DWORD) :
  let w := negB v in
  |-- basic
    (r~=v ** OSZCP?) (NEG r)
    (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) (v != #0) (lsb w)).
Proof.
  move => w. apply TRIPLE_basic => R. repeat autounfold with eval.
  rewrite /evalDst/evalDstR.
  triple_apply evalReg_rule.
  assert (HH := subB_equiv_addB_negB #0 v). rewrite /subB in HH.
  assert (CARRY := sbb0B_carry v).
  case E: (sbbB false #0 v) => [carry res].
  rewrite E in HH. rewrite E in CARRY. simpl snd in HH. simpl fst in CARRY.
  rewrite add0B in HH. rewrite HH.
  rewrite CARRY.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS. rewrite /w.
  triple_apply triple_setRegSep.
Qed.

(*---------------------------------------------------------------------------
    ADD and SUB instructions
  ---------------------------------------------------------------------------*)
(* Generic ADD/SUB rule *)
Lemma ADDSUB_rule isSUB d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d (if isSUB then OP_SUB else OP_ADD) ds)
             (let: (carry,v) := (if isSUB then sbbB else adcB) false v1 v2 in
              D v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof.
  rewrite /specAtDstSrc.
  destruct ds.
  (* RR *)
  specintros => v2.
  autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply evalDWORDorBYTEReg_rule.
  rewrite /evalBinOp/evalArithOpNoCarry.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).
  (* RM *)
  rewrite /specAtMemSpec.
  elim:src => [optSIB offset].
  elim: optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].
(* Indexed *)
  + specintros => v2 pbase ixval.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    rewrite /evalBinOp/evalArithOpNoCarry.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).
(* Non-indexed *)
  + specintros => v2 pbase.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_letGetDWORDorBYTESep.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).
(* offset only *)
  + specintro => v2.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.  rewrite /evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).

  (* MR *)
  specintros => v2. rewrite /specAtMemSpecDst.
  elim:dst => [optSIB offset].
  case: optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].
(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
  (* RI *)
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply triple_pre_introFlags => o sf zf cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false _ _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).

  (* MI *)
  rewrite /specAtMemSpecDst.
  elim:dst => [optSIB offset].
  elim:optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].

(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false _ _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false _ _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false _ _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
Qed.

Ltac basicADDSUB :=
  try unfold makeBOP;
  match goal with
  | |- |-- basic ?p (@BOP ?d OP_ADD ?a) ?q => basicapply (@ADDSUB_rule false d a)
  | |- |-- basic ?p (@BOP ?d OP_SUB ?a) ?q => basicapply (@ADDSUB_rule true d a)
  | _ => idtac
  end.

(* Special cases *)
(* ADD r, v2 *)
Corollary ADD_RI_rule (r:Reg) v1 (v2:DWORD):
  |-- basic (r~=v1 ** OSZCP?) (ADD r, v2)
            (let: (carry,v) := adcB false v1 v2 in
             r~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.

Corollary ADD_RI_ruleNoFlags (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1) (ADD r1, v2) (r1~=addB v1 v2) @ OSZCP?.
Proof. apply: basicForgetFlags; apply ADD_RI_rule. Qed.

(* ADD r1, r2 *)
Corollary ADD_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (ADD r1, r2)
            (let: (carry,v) := adcB false v1 v2 in
             r1~=v ** r2~=v2 ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. basicADDSUB. sbazooka. elim: (adcB _) => [carry v]. by ssimpl. Qed.

Corollary ADD_RR_ruleNoFlags (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (ADD r1, r2)
            (r1~=addB v1 v2 ** r2~=v2 ** OSZCP?).
Proof.
rewrite /addB/dropmsb.
basicADDSUB.
elim: (adcB _) => [carry v].
rewrite /OSZCP/stateIsAny. simpl snd. sbazooka.
Qed.

Corollary ADD_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (ADD r1, [r2 + offset])
            (let: (carry,v) := adcB false v1 v2 in
             r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. elim: (adcB _) => [carry v]. by ssimpl. Qed.

Corollary ADD_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (ADD r1, [r2 + offset]) (r1~=addB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof.
autorewrite with push_at.
basicADDSUB.
rewrite /OSZCP/stateIsAny/addB/dropmsb/snd.
elim: (adcB _) => [carry v].
sbazooka.
Qed.

Lemma SUB_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (SUB r1, [r2 + offset])
            (let: (carry,v) := sbbB false v1 v2 in
             r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. elim (sbbB _) => [carry v]. by ssimpl. Qed.

Corollary SUB_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (SUB r1, [r2 + offset]) (r1~=subB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof.
autorewrite with push_at. rewrite /subB.
elim E: (sbbB _ _ _) => [carry v].
basicADDSUB.
rewrite /OSZCP/stateIsAny/snd E. sbazooka.
Qed.

Lemma SUB_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (SUB r1, r2)
            (let: (carry,v) := sbbB false v1 v2 in r1~=v  ** r2~=v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. elim (sbbB _ _ _) => [carry v]. by ssimpl. Qed.

Lemma SUB_RI_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** OSZCP?) (SUB r1, v2)
            (let: (carry,v) := sbbB false v1 v2 in
             r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.

(*---------------------------------------------------------------------------
    CMP instruction
  ---------------------------------------------------------------------------*)

(* Generic rule *)
Lemma CMP_rule d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d OP_CMP ds)
             (let: (carry,v) := sbbB false v1 v2 in
              D v1 ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof.
  rewrite /specAtDstSrc.
  destruct ds.
  (* RR *)
  specintros => v2.
  autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply evalDWORDorBYTEReg_rule.
  rewrite /evalBinOp/evalArithOpNoCarry.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  elim: (_ false v1 v2) => [carry v].
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS. triple_apply triple_skip.
  (* RM *)
  rewrite /specAtMemSpec.
  elim:src => [optSIB offset].
  elim: optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].
(* Indexed *)
  + specintros => v2 pbase ixval.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    rewrite /evalBinOp/evalArithOpNoCarry.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Non-indexed *)
  + specintros => v2 pbase.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_letGetDWORDorBYTESep.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* offset only *)
  + specintro => v2.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.  rewrite /evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).

  (* MR *)
  specintros => v2. rewrite /specAtMemSpecDst.
  elim:dst => [optSIB offset].
  case: optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].
(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
  (* RI *)
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply triple_pre_introFlags => o sf zf cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false _ _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).

  (* MI *)
  rewrite /specAtMemSpecDst.
  elim:dst => [optSIB offset].
  elim:optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].

(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false _ _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false _ _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false _ _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
Qed.

Lemma sbbB_ZC n (r : BITS n) carry (v1 v: BITS n) :
  sbbB false v1 v = (carry, r) ->
   ZF~=(r == #(0)) ** CF~=carry |-- CF~=ltB v1 v ** ZF~=(v1 == v).
Proof. move => E.
  have S0 := subB_eq0 v1 v. rewrite /subB E/snd in S0. rewrite S0.
  have HH := (sbbB_ltB_leB v1 v). rewrite E/fst in HH.
  destruct carry. + rewrite HH. by ssimpl. + rewrite ltBNle HH /negb. by ssimpl.
Qed.

(* Generic rule with C and Z flags determining ltB and equality respectively *)
Lemma CMP_ruleZC d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d OP_CMP ds)
             (D v1 ** OF? ** SF? ** PF? ** CF ~= ltB v1 v2 ** ZF ~= (v1==v2))).
Proof.
have C := (CMP_rule ds) v1. rewrite /specAtDstSrc in C. rewrite /specAtDstSrc.
destruct ds.
+ specintros => v. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
+ destruct src as [optSIB offset].
  destruct optSIB as [[base ixopt] |].
  destruct ixopt as [[ixr sc] |].
  rewrite /specAtMemSpec. rewrite /specAtMemSpec in C.
  specintros => v pbase ixval. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  rewrite /specAtMemSpec. rewrite /specAtMemSpec in C.
  specintros => v pbase. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  rewrite /specAtMemSpec. rewrite /specAtMemSpec in C.
  specintros => v. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  specintros => v. rewrite /specAtMemSpecDst. rewrite /specAtMemSpecDst in C.
  destruct dst as [optSIB offset].
  destruct optSIB as [[base ixopt] |].
  destruct ixopt as [[ixr sc] |].
  specintros => pbase ixval. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  specintros => pbase. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.

  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 c) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.

rewrite /specAtMemSpecDst. rewrite /specAtMemSpecDst in C.
  destruct dst as [optSIB offset].
  destruct optSIB as [[base ixopt] |].
  destruct ixopt as [[ixr sc] |].
  specintros => pbase ixval. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 c) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  specintros => pbase. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 c) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 c) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
Qed.

Ltac basicCMP :=
  try unfold makeBOP;
  match goal with
  | |- |-- basic ?p (@BOP ?d OP_CMP ?a) ?q => basicapply (@CMP_rule d a)
  | _ => idtac
  end.

Ltac basicCMP_ZC :=
  try unfold makeBOP;
  match goal with
  | |- |-- basic ?p (@BOP ?d OP_CMP ?a) ?q => basicapply (@CMP_ruleZC d a)
  | _ => idtac
  end.


(* Special cases *)
Lemma CMP_RI_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2)
            (let: (carry,res) := sbbB false v1 v2 in
             r1 ~= v1 ** OSZCP (computeOverflow v1 v2 res) (msb res)
                         (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.

Lemma CMP_RbI_rule (r1:BYTEReg) (v1 v2:BYTE):
  |-- basic (BYTEregIs r1 v1 ** OSZCP?) (CMP r1, v2)
            (let: (carry,res) := sbbB false v1 v2 in
  BYTEregIs r1 v1 ** OSZCP (computeOverflow v1 v2 res) (msb res) (res == #0) carry (lsb res)).
Proof. rewrite /BYTEtoDWORD/makeBOP low_catB. basicCMP. Qed.

Lemma CMP_RM_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP r1, [r2+offset])
            (let (carry,res) := sbbB false v1 v2 in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basicCMP.
case E: (sbbB false v1 v2) => [carry res].
sbazooka.
Qed.

Lemma CMP_MR_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP [r2+offset], r1)
            (let (carry,res) := sbbB false v2 v1 in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v2 v1 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basicCMP.
case E: (sbbB false v2 v1) => [carry res].
sbazooka.
Qed.

Lemma CMP_MR_ZC_rule (pd: DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OSZCP?) (CMP [r1+offset], r2)
            (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OF? ** SF? ** PF? **
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= v2 ** OSZCP?) (CMP r1, r2)
            (let: (carry,res) := sbbB false v1 v2 in
             r1 ~= v1 ** r2 ~= v2 **
              OSZCP (computeOverflow v1 v2 res) (msb res)
                    (res == #0) carry (lsb res)).
Proof. basicCMP. destruct (sbbB false v1 v2); by ssimpl. Qed.


Lemma CMP_RI_ZC_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2)
            (r1 ~= v1 ** OF? ** SF? ** PF? ** CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbR_ZC_rule (r1:Reg) (r2: BYTEReg) (p:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** BYTEregIs r2 v2 ** p :-> v1 ** OSZCP?) (CMP [r1], r2)
            (r1 ~= p ** BYTEregIs r2 v2 ** p :-> v1 ** OF? ** SF? ** PF? **
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbI_ZC_rule (r1:Reg) (p:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** p :-> v1 ** OSZCP?) (CMP BYTE [r1], v2)
            (r1 ~= p ** p :-> v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbxI_ZC_rule (r1:Reg) (r2:NonSPReg) (p ix:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** r2 ~= ix ** addB p ix :-> v1 ** OSZCP?) (CMP BYTE [r1 + r2 + 0], v2)
            (r1 ~= p ** r2 ~= ix ** addB p ix :-> v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC; rewrite /scaleBy; by ssimpl. Qed.


Lemma CMP_RbI_ZC_rule (r1:BYTEReg) (v1 v2:BYTE):
  |-- basic (BYTEregIs r1 v1 ** OSZCP?) (BOP false OP_CMP (DstSrcRI false r1 v2))
            (BYTEregIs r1 v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.


Lemma XOR_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (XOR r1, r2)
            (r1~=xorB v1 v2 ** r2~=v2 ** OSZCP false (msb (xorB v1 v2))
                            (xorB v1 v2 == #0) false (lsb (xorB v1 v2))).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval.
  triple_apply evalReg_rule.
  triple_apply evalReg_rule.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP/evalLogicalOp.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_setRegSep.
Qed.

Lemma ADC_RI_rule (r1:Reg) v1 (v2:DWORD) carry v o s z c p:
  adcB c v1 v2 = (carry,v) ->
  |-- basic (r1~=v1 ** OSZCP o s z c p) (ADC r1, v2)
            (r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval.
  triple_apply evalReg_rule.
  rewrite /OSZCP.
  triple_apply triple_letGetFlag.
  - by ssimpl.
  rewrite E.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_setRegSep.
Qed.

(*---------------------------------------------------------------------------
    AND instruction
  ---------------------------------------------------------------------------*)
(* Generic AND *)
Lemma AND_rule (ds:DstSrc true) (v1: DWORD) :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP true OP_AND ds)
             (let v:= andB v1 v2 in
              D v ** OSZCP false (msb v) (v == #0) false (lsb v))).
Proof.
  rewrite /specAtDstSrc/DWORDorBYTEregIs.
  destruct ds.
  (* RR *)
  specintros => v2. autorewrite with push_at. apply TRIPLE_basic => R.
  repeat (autounfold with eval).
  triple_apply evalReg_rule.
  triple_apply evalReg_rule.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_setRegSep.
  (* RM *)
  rewrite /specAtMemSpec.
  elim:src => [optSIB offset].
  elim: optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].
(* Indexed *)
  + specintros => v2 pbase ixval.
    autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval).
    triple_apply evalReg_rule.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doUpdateZPS.
    triple_apply triple_setRegSep.
(* Non-indexed *)
  + specintros => v2 pbase.
    autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval).
    rewrite /evalDstSrc/evalDstR.
    triple_apply evalReg_rule.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doUpdateZPS.
    triple_apply triple_setRegSep.
(* Offset only *)
  + specintros => v2.
    autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval).
    rewrite /evalDstSrc/evalDstR.
    triple_apply evalReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalMemSpec.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doUpdateZPS.
    triple_apply triple_setRegSep.
  (* MR *)
  specintros => v2. rewrite /specAtMemSpecDst.
  elim:dst => [optSIB offset].
  elim:optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].
(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply evalReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doUpdateZPS.
    triple_apply triple_setDWORDSep.
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply evalReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doUpdateZPS.
    triple_apply triple_setDWORDSep.
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDSep.
    triple_apply evalReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doUpdateZPS.
    triple_apply triple_setDWORDSep.
  (* RI *)
  apply TRIPLE_basic => R.
  repeat (autounfold with eval).  rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule.
  triple_apply triple_pre_introFlags => o sf zf cf pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_setRegSep.

  (* MI *)
  rewrite /specAtMemSpecDst.
  elim:dst => [optSIB offset].
  elim:optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].

(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doUpdateZPS.
    triple_apply triple_setDWORDSep.
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doUpdateZPS.
    triple_apply triple_setDWORDSep.
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doUpdateZPS.
    triple_apply triple_setDWORDSep.
Qed.

(* AND r1, r2 *)
Corollary AND_RR_rule (r1 r2:Reg) v1 (v2:DWORD) :
  |-- basic (r1~=v1 ** r2 ~= v2 ** OSZCP?)
            (AND r1, r2)
            (let v := andB v1 v2 in r1~=v ** r2 ~= v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. basicapply (AND_rule (DstSrcRR true r1 r2)). Qed.

(* AND r1, [r2 + offset] *)
Corollary AND_RM_rule (pbase:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) :
  |-- basic (r1~=v1 ** OSZCP?)
            (AND r1, [r2 + offset])
            (let v:= andB v1 v2 in r1~=v ** OSZCP false (msb v) (v == #0) false (lsb v))
      @ (r2 ~= pbase ** pbase +# offset :-> v2).
Proof.
  autorewrite with push_at.
  basicapply (AND_rule (DstSrcRM true r1 (mkMemSpec (Some(r2, None)) #offset))).
Qed.

Corollary AND_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (AND r1, [r2 + offset]) (r1~=andB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof.
autorewrite with push_at.
basicapply (AND_RM_rule (pbase:=pd) (r1:=r1) (r2:=r2) (v1:=v1) (v2:=v2) (offset:=offset)).
rewrite /OSZCP/stateIsAny/snd. sbazooka.
Qed.


(* AND r, v *)
Lemma AND_RI_rule (r:Reg) v1 (v2:DWORD) :
  |-- basic (r~=v1 ** OSZCP?)
            (AND r, v2)
            (let v:= andB v1 v2 in r~=v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. basicapply (AND_rule (DstSrcRI true r v2)). Qed.


Lemma OR_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  orB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (OR r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule.
  unfold natAsDWORD.
  triple_apply evalMemSpecNone_rule.
  triple_apply triple_letGetDWORDSep.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep. rewrite E.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_setRegSep.
Qed.

Lemma XOR_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  xorB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (XOR r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  (* Copy-paste of OR_RM_rule proof *)
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule.
  triple_apply evalMemSpecNone_rule.
  unfold natAsDWORD.
  triple_apply triple_letGetDWORDSep.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep. rewrite E.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_setRegSep.
Qed.

Corollary OR_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (OR r1, [r2 + offset]) (r1~=orB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof.
autorewrite with push_at.
basicapply (@OR_RM_rule pd r1 r2 v1 v2 offset (orB v1 v2) (refl_equal _)).
rewrite /OSZCP/stateIsAny/snd. sbazooka.
Qed.

Corollary XOR_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (XOR r1, [r2 + offset]) (r1~=xorB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof.
autorewrite with push_at.
basicapply (@XOR_RM_rule pd r1 r2 v1 v2 offset (xorB v1 v2) (refl_equal _)).
rewrite /OSZCP/stateIsAny/snd. sbazooka.
Qed.


Lemma TEST_self_rule (r:Reg) (v:DWORD) :
  |-- basic (r ~= v ** OSZCP?) (TEST r, r)
            (r ~= v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDst/evalDstR/evalRegImm.
  triple_apply evalReg_rule.
  triple_apply evalReg_rule. rewrite andBB.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_skip.
Qed.


(* Lazy man's proof *)
Lemma SmallCount : forall count, count < 32 -> toNat (n:=8) (andB #x"1f" (fromNat count)) = count.
Proof. do 32 case => //.
Qed.

Lemma SHL_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 ->
  |-- basic (r~=v ** OSZCP?) (SHL r, count)
            (r~=iter count shlB v ** OSZCP?).
Proof.
  move => BOUND.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDst/evalDstR.
  triple_apply evalReg_rule.
  rewrite /evalShiftCount/evalShiftOp. rewrite id_l.
  rewrite (SmallCount BOUND).
  case E: count => [| count'].
  + replace (iter _ _ v) with v by done.
    triple_apply triple_setRegSep.


  triple_apply triple_pre_introFlags => o s z c p.
  rewrite /OSZCP/stateIsAny.
  triple_apply triple_doSetFlagSep.
  case E': count' => [| count''].
  + triple_apply triple_doSetFlagSep.
    triple_apply triple_setRegSep. rewrite dropmsb_iter_shlB.
    sbazooka.
  + triple_apply triple_doForgetFlagSep.
    triple_apply triple_setRegSep.
    rewrite dropmsb_iter_shlB.
    rewrite /stateIsAny. sbazooka.
Qed.

Lemma SHR_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 ->
  |-- basic (r~=v ** OSZCP?) (SHR r, count)
            (r~=iter count shrB v ** OSZCP?).
Proof.
  move => BOUND.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR.
  triple_apply evalReg_rule.
  rewrite /evalShiftCount/evalShiftOp id_l.
  rewrite (SmallCount BOUND).
  case E: count => [| count'].
  + replace (iter _ _ v) with v by done.
    triple_apply triple_setRegSep.


  triple_apply triple_pre_introFlags => o s z c p.
  rewrite /OSZCP/stateIsAny.
  triple_apply triple_doSetFlagSep.
  case E': count' => [| count''].
  + triple_apply triple_doSetFlagSep.
    triple_apply triple_setRegSep. rewrite droplsb_iter_shrB.
    sbazooka.
  + triple_apply triple_doForgetFlagSep.
    triple_apply triple_setRegSep.
    rewrite droplsb_iter_shrB.
    rewrite /stateIsAny. sbazooka.
Qed.

(*---------------------------------------------------------------------------
    Now, rules that involve control-flow.
  ---------------------------------------------------------------------------*)

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

Lemma triple_letGetCondition cc (v:bool) (P Q: SPred) c:
  TRIPLE (ConditionIs cc v ** P) (c v) Q ->
  TRIPLE (ConditionIs cc v ** P) (bind (evalCondition cc) c) Q.
Proof.
  rewrite /evalCondition /ConditionIs => H. destruct cc.
  - (* CC_O *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_C *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_Z *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_BE *)
    apply triple_pre_existsSep => fc. triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fz. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv.
    subst v.
    triple_apply H; sbazooka.
  - (* CC_S *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_P *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_L *)
    apply triple_pre_existsSep => fs. triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fo. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. subst v.
    triple_apply H; sbazooka.
  - (* CC_LE *)
    apply triple_pre_existsSep => fs. triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fo. triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fz. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. subst v.
    triple_apply H; sbazooka.
Qed.

Lemma JMPrel_rule (tgt: JmpTgt) (p q: DWORD) :
  |-- interpJmpTgt tgt q (fun P addr =>
     (|> safe @ (EIP ~= addr ** P) -->> safe @ (EIP ~= p ** P)) <@ (p -- q :-> JMPrel tgt)).
Proof.
  rewrite /interpJmpTgt. destruct tgt.
  (* JmpTgtI *)
  destruct t. apply TRIPLE_safe => R.
  rewrite /evalInstr/evalSrc/evalJmpTgt.
  triple_apply triple_letGetRegSep.
  triple_apply triple_setRegSep.

  (* JmpTgtM *)
  destruct m.
  case: sib => [[base indexAndScale] |].
  - destruct indexAndScale.
    destruct p0 as [rix sc].
    rewrite /interpMemSpecSrc.
    specintros => pase ixval addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr/evalJmpTgt/evalMemSpec/evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetDWORDSep.
    by triple_apply triple_setRegSep.
    rewrite /interpMemSpecSrc.
    specintros => pbase addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr/evalJmpTgt/evalMemSpec/evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetDWORDSep.
    by triple_apply triple_setRegSep.
    rewrite /interpMemSpecSrc.
    specintros => addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr/evalJmpTgt/evalMemSpec/evalRegMem /evalReg.
    triple_apply triple_letGetDWORDSep.
    by triple_apply triple_setRegSep.

  (* JmpTgtR *)
  specintros => addr.
  apply TRIPLE_safe => R.
  rewrite /evalInstr/evalJmpTgt /evalRegMem /evalReg /evalPush.
  triple_apply triple_letGetRegSep.
  by triple_apply triple_setRegSep.
Qed.


(* For convenience, the ~~b branch is not under a |> operator since q will
   never be equal to p, and thus there is no risk of recursion. *)
Lemma JCCrel_rule rel cc cv (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (b == cv /\\ EIP ~= (addB q rel) ** ConditionIs cc b) //\\
         safe @ (b == (~~cv) /\\ EIP ~= q ** ConditionIs cc b) -->>
      safe @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCCrel cc cv (mkTgt rel)).
Proof.
  Import Setoid.
  rewrite ->(spec_later_weaken (safe @ (b == (~~ cv) /\\ EIP~=q ** ConditionIs cc b))).
  rewrite <-spec_later_and. rewrite ->spec_at_and_or; last apply _.
  apply TRIPLE_safe => R. rewrite /evalInstr.
  triple_apply triple_letGetCondition.
  replace (b == (~~cv)) with (~~(b == cv)); last first.
  - case: b; case: cv; reflexivity.
  case: (b == cv).
  - triple_apply triple_letGetRegSep.
    triple_apply triple_setRegSep.
    apply: lorR1. ssplit => //.
  - triple_apply triple_skip.
    apply: lorR2. by sbazooka.
Qed.

Lemma RET_rule p' (sp:DWORD) (offset:WORD) (p q: DWORD) :
  let sp':DWORD := addB (sp+#4) (zeroExtend 16 offset) in
  |-- (
      |> safe @ (EIP ~= p' ** ESP ~= sp' ** sp :-> p') -->>
         safe @ (EIP ~= p  ** ESP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RETOP offset).
Proof.
  apply TRIPLE_safe => R.
  rewrite /evalInstr.
  triple_apply triple_letGetRegSep.
  triple_apply triple_letGetDWORDSep.
  triple_apply triple_doSetRegSep.
  triple_apply triple_setRegSep.
Qed.

Lemma CALLrel_rule (p q: DWORD) (tgt: JmpTgt) (w sp:DWORD) :
  |-- interpJmpTgt tgt q (fun P p' =>
      (
      |> safe @ (EIP ~= p' ** P ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** P ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel tgt)).
Proof.
  rewrite /interpJmpTgt.
  destruct tgt.

  (* JmpTgtI *)
  destruct t.
  apply TRIPLE_safe => R.
  rewrite /evalInstr /evalRegMem /evalReg.
  triple_apply triple_letGetRegSep.
  rewrite /evalJmpTgt.
  triple_apply triple_letGetRegSep.
  triple_apply triple_doSetRegSep.
  by triple_apply evalPush_rule.

  (* JmpTgtM *)
  destruct m.
  - case: sib => [[base indexAndScale] |].
    destruct indexAndScale.
    destruct p0 as [rix sc].
    rewrite /interpMemSpecSrc. specintros => pbase indexval addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr /evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    rewrite /evalJmpTgt/evalMemSpec.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetRegSep.
    by triple_apply evalPush_rule.
    rewrite /interpMemSpecSrc. specintros => pbase addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr /evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    rewrite /evalJmpTgt/evalMemSpec.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetRegSep.
    by triple_apply evalPush_rule.
    rewrite /interpMemSpecSrc. specintros => addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr /evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    rewrite /evalJmpTgt/evalMemSpec.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetRegSep.
    by triple_apply evalPush_rule.

  (* JmpTgtR *)
  specintros => addr.
  apply TRIPLE_safe => R.
  rewrite /evalInstr /evalRegMem /evalReg.
  triple_apply triple_letGetRegSep.
  triple_apply triple_letGetRegSep.
  triple_apply triple_doSetRegSep.
  by triple_apply evalPush_rule.
Qed.

Corollary CALLrel_R_rule (r:Reg) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, Forall p', (
      |> safe @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof.
  specintros => w sp p'.
  Hint Unfold interpJmpTgt : specapply.
  specapply (CALLrel_rule p q (JmpTgtR r)). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.

Corollary CALLrel_I_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, (
      |> safe @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof.
  specintros => w sp.
  specapply (CALLrel_rule p q (JmpTgtI rel)). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.


(* unconditional jump *)
Lemma JMPrel_I_rule rel (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addB q rel) -->> safe @ (EIP ~= p)) <@
        (p -- q :-> JMPrel (mkTgt rel)).
Proof.
  specapply (JMPrel_rule (JmpTgtI (mkTgt rel))). by ssimpl.

  autorewrite with push_at. rewrite <-spec_reads_frame. apply limplValid.
  cancel1. cancel1. sbazooka.
Qed.

Lemma JMPrel_R_rule (r:Reg) addr (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addr ** r ~= addr) -->> safe @ (EIP ~= p ** r ~= addr)) <@
        (p -- q :-> JMPrel (JmpTgtR r)).
Proof.
  specapply (JMPrel_rule (JmpTgtR r)). by ssimpl.

  rewrite <-spec_reads_frame. autorewrite with push_at. rewrite limplValid.
  cancel1. cancel1. sbazooka.
Qed.

End InstrRules.