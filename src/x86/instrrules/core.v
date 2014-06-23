(*===========================================================================
    Rules for x86 instructions in terms of [safe]
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
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
  forall s: ProcState, (P ** ltrue) (toPState s) ->
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
    move => Hsij HTRIPLE k R HQ. rewrite /spec_fun /= in HQ. move=> s Hs.
    destruct k. (* everything's safe in 0 steps *)
    - exists s. exists nil. reflexivity.
    rewrite /doMany -/doMany.
    (* TODO: This is clumsy. Make it more like in attic/instrrules.v. *)
    move: s Hs. apply: TRIPLE_nopost.
    rewrite assoc. eapply triple_letGetReg.
    - by ssimpl.
    rewrite assoc.
    eapply triple_letReadSep.
    - rewrite ->Hsij. by ssimpl.
    rewrite assoc. eapply triple_seq.
    - eapply triple_setRegSepGen. by ssimpl.
    eapply triple_seq.
    - triple_apply HTRIPLE.
    move=> s Hs.
    edestruct (HQ k) as [f [o Hf]]; first omega.
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

Hint Unfold interpJmpTgt : specapply.

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
try_triple_apply S; sbazooka. Qed.

Lemma evalBYTERegAux_rule (r: BYTEReg) d v c Q :
  forall S,
  TRIPLE (BYTEregIsAux r d v ** S) (c v) Q ->
  TRIPLE (BYTEregIsAux r d v ** S) (bind (evalBYTEReg r) c) Q.
Proof.
rewrite /evalBYTEReg/BYTEregIsAux.
move => S T.
destruct r; try_triple_apply triple_letGetReg; sbazooka.
+ try_triple_apply (@triple_preEq _ (low 8 d) v (EAX~=d ** S)); sbazooka.
  try_triple_apply T; sbazooka.
+ try_triple_apply (@triple_preEq _ (low 8 d) v (EBX~=d ** S)); sbazooka.
  try_triple_apply T; sbazooka.
+ try_triple_apply (@triple_preEq _ (low 8 d) v (ECX~=d ** S)); sbazooka.
  try_triple_apply T; sbazooka.
+ try_triple_apply (@triple_preEq _ (low 8 d) v (EDX~=d ** S)); sbazooka.
  try_triple_apply T; sbazooka.
+ try_triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (EAX~=d ** S)); sbazooka.
  try_triple_apply T; sbazooka.
+ try_triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (EBX~=d ** S)); sbazooka.
  try_triple_apply T; sbazooka.
+ try_triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (ECX~=d ** S)); sbazooka.
  try_triple_apply T; sbazooka.
+ try_triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (EDX~=d ** S)); sbazooka.
  try_triple_apply T; sbazooka.
Qed.

Lemma evalBYTEReg_rule (r: BYTEReg) v c Q :
  forall S,
  TRIPLE (BYTEregIs r v ** S) (c v) Q ->
  TRIPLE (BYTEregIs r v ** S) (bind (evalBYTEReg r) c) Q.
Proof.
move => S T.
apply triple_pre_existsSep => d.
triple_apply evalBYTERegAux_rule. rewrite /BYTEregIs in T.
try_triple_apply T; sbazooka.
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
  triple_apply triple_letGetRegSep; try_triple_apply triple_setRegSep.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.
Qed.

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

Lemma triple_letGetDWORDorBYTESep d (p:PTR) (v:DWORDorBYTE d) c Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) Q ->
  TRIPLE (p:->v ** S) (bind (getDWORDorBYTEFromProcState _ p) c) Q.
Proof. destruct d; [apply triple_letGetSep | apply triple_letGetBYTESep]. Qed.

Lemma basicForgetFlags T (MI: MemIs T) P (x:T) Q o s z c p:
  |-- basic (P ** OSZCP?) x (Q ** OSZCP o s z c p) ->
  |-- basic P x Q @ OSZCP?.
Proof. move => H. autorewrite with push_at.
basicapply H. rewrite /OSZCP/stateIsAny. sbazooka.
Qed.

Lemma sbbB_ZC n (r : BITS n) carry (v1 v: BITS n) :
  sbbB false v1 v = (carry, r) ->
   ZF~=(r == #(0)) ** CF~=carry |-- CF~=ltB v1 v ** ZF~=(v1 == v).
Proof. move => E.
  have S0 := subB_eq0 v1 v. rewrite E/snd in S0. rewrite S0.
  have HH := (sbbB_ltB_leB v1 v). rewrite E/fst in HH.
  destruct carry. + rewrite HH. by ssimpl. + rewrite ltBNle HH /negb. by ssimpl.
Qed.

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
    apply triple_pre_existsSep => fc. try_triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fz. try_triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv.
    subst v.
    try_triple_apply H; sbazooka.
  - (* CC_S *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_P *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_L *)
    apply triple_pre_existsSep => fs. try_triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fo. try_triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. subst v.
    try_triple_apply H; sbazooka.
  - (* CC_LE *)
    apply triple_pre_existsSep => fs. try_triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fo. try_triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fz. try_triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. subst v.
    try_triple_apply H; sbazooka.
Qed.
End InstrRules.
