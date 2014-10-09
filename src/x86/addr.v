(*===========================================================================
    Address type
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.finfun Ssreflect.eqtype Ssreflect.fintype Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* In 64-bit mode there are two address sizes: 32-bit and 64-bit *)
Inductive AdSize := AdSize4 | AdSize8.
Definition adSizeToOpSize a := match a with AdSize4 => OpSize4 | AdSize8 => OpSize8 end.
Definition ADR a := VWORD (adSizeToOpSize a).
Identity Coercion ADRtoVWORD : ADR >-> VWORD.

(* Default address type for 64-bit more. 
   @TODO: what do we do about canonical addressing (see 3.3.7.1)? *)
Definition naddrBits := n64.

Definition ADDR := QWORD.
Identity Coercion ADDRtoQWORD : ADDR >-> QWORD.

Definition ADDRCursor := QWORDCursor.
Identity Coercion ADDRCursortoQWORDCUrsor : ADDRCursor >-> QWORDCursor. 

Definition (*Coercion*) ADDRtoADDRCursor (x:ADDR) : ADDRCursor := mkCursor x.
Definition (*Coercion*) ADRtoADDR a  :=
  match a return ADR a -> ADDR with 
  | AdSize4 => fun x => zeroExtend 32 x
  | AdSize8 => fun x => x
  end.


