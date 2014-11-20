(*===========================================================================
    Address type
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.finfun Ssreflect.eqtype Ssreflect.fintype Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* In 64-bit mode there are two sizes for effective addresses: 32-bit and 64-bit *)
(* This offset is added to the 64-bit segment base (0, except for FS and GS) *)
Inductive AdSize := AdSize4 | AdSize8.
Definition adSizeToOpSize a := match a with AdSize4 => OpSize4 | AdSize8 => OpSize8 end.

(* Address offset, before widening and adding to segment base *)
Definition ADR a := VWORD (adSizeToOpSize a).
Identity Coercion ADRtoVWORD : ADR >-> VWORD.

(* Default address type for 64-bit more. 
   @TODO: what do we do about canonical addressing (see 3.3.7.1)? *)
Definition naddrBits := n64.

(* Logical address, after adding in segment base *)
Definition ADDR := QWORD.
Identity Coercion ADDRtoQWORD : ADDR >-> QWORD.

Definition ADDRCursor := QWORDCursor.
Identity Coercion ADDRCursortoQWORDCUrsor : ADDRCursor >-> QWORDCursor. 

Definition (*Coercion*) ADDRtoADDRCursor (x:ADDR) : ADDRCursor := mkCursor x.
Definition (*Coercion*) ADRtoADDR a  :=
  match a return ADR a -> ADDR with 
  | AdSize4 => fun x => zeroExtend n32 x
  | AdSize8 => fun x => x
  end.
Definition (*Coercion*) ADDRtoADR a  :=
  match a return ADDR -> ADR a with 
  | AdSize4 => fun x => low n32 x
  | AdSize8 => fun x => x
  end.


