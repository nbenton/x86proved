(** * Pointedness of charge.ilogic things *)
Require Import Ssreflect.ssreflect.
Require Import x86proved.charge.ilogic.
Require Import x86proved.pointed.

Generalizable All Variables.

Section ilogic.
  Context `{@ILogic Frm ILOps}.

  Global Instance IsPointed_ltrueR: forall C, IsPointed (C |-- ltrue) := ltrueR.
  Global Instance IsPointed_lfalseL: forall C, IsPointed (lfalse |-- C) := lfalseL.
  (*Global Instance IsPointed_lforallL: forall T `{IsPointed T} (P: T -> Frm) C `{IsPointed (P (point T) |-- C)}, IsPointed (lforall P |-- C) := lforallL.*)
  Global Instance IsPointed_lforallR: forall T (P: T -> Frm) C `{forall x, IsPointed (C |-- P x)}, IsPointed (C |-- lforall P) := lforallR.
  Global Instance IsPointed_lexistsL: forall T (P: T -> Frm) C `{forall x, IsPointed (P x |-- C)}, IsPointed (lexists P |-- C) := lexistsL.
  (*Global Instance IsPointed_lexistsR: forall T `{IsPointed T} (P: T -> Frm) C `{IsPointed (C |-- P (point T))}, IsPointed (C |-- lexists P) := lexistsR.*)
  (*Global Instance IsPointed_landL1: forall P Q C, P |-- C  ->  IsPointed (P //\\ Q |-- C;
  Global Instance IsPointed_landL2: forall P Q C, Q |-- C  ->  IsPointed (P //\\ Q |-- C;
  Global Instance IsPointed_lorR1:  forall P Q C, C |-- P  ->  IsPointed (C |-- P \\// Q;
  Global Instance IsPointed_lorR2:  forall P Q C, C |-- Q  ->  IsPointed (C |-- P \\// Q;*)
  Global Instance IsPointed_landR:  forall P Q C `{IsPointed (C |-- P), IsPointed (C |-- Q)}, IsPointed (C |-- P //\\ Q) := landR.
  Global Instance IsPointed_lorL:   forall P Q C `{IsPointed (P |-- C), IsPointed (Q |-- C)}, IsPointed (P \\// Q |-- C) := lorL.
  (*Global Instance IsPointed_landAdj: forall P Q C, C |-- (P -->> Q) -> IsPointed (C //\\ P |-- Q;*)
  (** We want to remove [limpl]s when trying to find pointed instances *)
  Global Instance IsPointed_limplAdj: forall P Q C `{IsPointed (C //\\ P |-- Q)}, IsPointed (C |-- (P -->> Q)) := limplAdj.
End ilogic.
