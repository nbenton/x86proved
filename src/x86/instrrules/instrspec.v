(*===========================================================================
    Helper definitions used in specification of instructions
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.bitsops.
Require Import x86proved.spec x86proved.spred.
Require Import x86proved.cursor.
Require Import x86proved.x86.instr x86proved.x86.eval.
Require Import x86proved.common_definitions x86proved.common_tactics.

Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.

Global Set Implicit Arguments.
Global Unset Strict Implicit.

Import Prenex Implicits.

Notation "OSZCP?" := (OF? ** SF? ** ZF? ** CF? ** PF?).
Definition OSZCP o s z c p := OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p.

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

Definition interpUIP a : Reg (adSizeToOpSize a) := match a with AdSize4 => EIP | AdSize8 => RIP end.

(* Hint database for specAtX definitions *)
Create HintDb specAt.

(* We define specAtX for every X that has an evalX definition in eval.v *)
Definition specAtSegBase a (sreg: SegReg) (f: ADR a -> spec) : spec :=
  Forall segsel gdtr segbase, 
  f segbase @ (GDTR ~= gdtr ** sreg ~= segsel ** addB gdtr (zeroExtend _ segsel) :-> segbase).
Hint Unfold specAtSegBase : specAt.

Definition specAtBaseReg a (optBaseReg: option (BaseReg a)) (f: ADR a -> spec) :=
  if optBaseReg is Some baseReg 
  then Forall base, f base @ ((baseReg:GPReg _) ~= base)
  else f #0.
Hint Unfold specAtBaseReg : specAt.

Definition specAtIndexAndScale a (ixSpec : option (IxReg a * Scale)) (f: option (ADR a * Scale) -> spec) :=
  if ixSpec is Some(ixReg,sc)
  then Forall ixval, f (Some(ixval, sc)) @ ((ixReg:NonSPReg _) ~= ixval)
  else f None.
Hint Unfold specAtIndexAndScale : specAt.

Definition specAtMemSpecEA a (ms: MemSpec a) (f: ADR a -> spec) : spec :=
  match ms with
  (* RIP-relative addressing needs special treatment as it talks about RIP *)
  | RIPrel _ => ltrue

  | mkMemSpec _ optBase optIxScale disp =>
    specAtBaseReg optBase (fun base =>
    specAtIndexAndScale optIxScale (fun ixVal =>
    f (computeEA base ixVal disp)))
  end.
Hint Unfold specAtMemSpecEA : specAt.

Definition specAtMemSpec a (ms: MemSpec a) (f: ADDR -> spec) :=
  specAtMemSpecEA ms (fun offset =>
  if ms is mkMemSpec (Some sreg) _ _ _
  then 
    specAtSegBase sreg (fun segbase =>
    f (ADRtoADDR (addB segbase offset)))
  else
    f (ADRtoADDR offset)).
Hint Unfold specAtMemSpec : specAt.

Definition specAtMemSpecSrc s a (ms: MemSpec a) (f: VWORD s -> spec) :=
  specAtMemSpec ms (fun p =>
  Forall v, f v @ (p :-> v)).
Hint Unfold specAtMemSpecSrc : specAt.

Definition specAtMemSpecDst s a (ms:MemSpec a) (f: (VWORD s -> SPred) -> spec) :=
  specAtMemSpec ms (fun p => f (fun v => p :-> v)).
Hint Unfold specAtMemSpecDst : specAt.

Definition specAtRegMemDst s (src: RegMem s) (f: (VWORD s -> SPred) -> spec) :spec  :=
  match src with
  | RegMemR r =>
    f (fun v => r ~= v)

  | RegMemM a ms =>
    specAtMemSpecDst ms f
  end.
Hint Unfold specAtRegMemDst : specAt.

Definition specAtJmpTgt (tgt: JmpTgt AdSize8) (nextInstr: ADDR) (f: ADR AdSize8 -> spec) :=
  match tgt with
  | JmpTgtI t =>
    let: mkTgt d := t in
    f (addB nextInstr d)

  | JmpTgtRegMem (RegMemR r) =>
    Forall addr,
    f addr @ (r ~= addr)

  | JmpTgtRegMem (RegMemM _ ms) =>
    specAtMemSpecSrc ms f
  end.
Hint Unfold specAtJmpTgt : specAt.

Definition specAtSrc s (src: Src s) (f: VWORD s -> spec) : spec :=
  match src with
  | SrcI v =>
    f (getImm v)

  | SrcR r =>
    Forall v,
    f v @ (r ~= v)

  | SrcM a ms =>
    specAtMemSpecSrc ms f
  end.
Hint Unfold specAtSrc : specAt.

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
    specAtMemSpecSrc src (fun v => f (fun w => dst ~= w) v)
  end.
Hint Unfold specAtDstSrc : specAt.

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
    specAtMemSpecSrc src (fun v => f (fun w => dst ~= w) v)
  end.
Hint Unfold specAtMovDstSrc : specAt.

Local Ltac specAt_morphism_step :=
  idtac;
  do [ progress move => *
     | hyp_setoid_rewrite -> *; reflexivity
     | progress autounfold with specAt
     | progress destruct_head DstSrc
     | progress destruct_head MovDstSrc
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
Proof. specAt_morphism_t => //. Qed.

Add Parametric Morphism a s ms : (@specAtMemSpecDst a s ms)
with signature pointwise_relation _ (Basics.flip lentails) ++> Basics.flip lentails
  as specAtMemSpecDst_flip_entails_m.
Proof. specAt_morphism_t => //. Qed.

Add Parametric Morphism a s ms : (@specAtMemSpecSrc a s ms)
with signature pointwise_relation _ lentails ++> lentails
  as specAtMemSpec_entails_m.
Proof.  specAt_morphism_t => //. Qed.

Add Parametric Morphism a s ms : (@specAtMemSpecSrc a s ms)
with signature pointwise_relation _ (Basics.flip lentails) ++> Basics.flip lentails
  as specAtMemSpec_flip_entails_m.
Proof. specAt_morphism_t => //. Qed.

Add Parametric Morphism s ms : (@specAtDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ lentails) ++> lentails
  as specAtDstSrc_entails_m.
Proof. specAt_morphism_t => //. Qed.

Add Parametric Morphism s ms : (@specAtDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ (Basics.flip lentails)) ++> Basics.flip lentails
  as specAtDstSrc_flip_entails_m.
Proof. specAt_morphism_t => //. Qed.

Add Parametric Morphism s ms : (@specAtMovDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ lentails) ++> lentails
  as specAtMovDstSrc_entails_m.
Proof. specAt_morphism_t => //. Qed.

Add Parametric Morphism s ms : (@specAtMovDstSrc s ms)
with signature pointwise_relation _ (pointwise_relation _ (Basics.flip lentails)) ++> Basics.flip lentails
  as specAtMovDstSrc_flip_entails_m.
Proof. specAt_morphism_t => //. Qed.

