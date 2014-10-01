(*===========================================================================
    Address type
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.finfun Ssreflect.eqtype Ssreflect.fintype Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Address type for x86.
   When we move to x64 what should we do about canonical addressing (see 3.3.7.1)? *)
Definition naddrBits := n32.
Definition ADDR := DWORD.
Identity Coercion ADDRtoDWORD : ADDR >-> DWORD.

(* Cursor type for x86. *)
Definition ADDRCursor := DWORDCursor.
Identity Coercion ADDRCursorToDWORDCursor : ADDRCursor >-> DWORDCursor.

