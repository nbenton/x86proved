(*===========================================================================
  Lists
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.safe x86proved.x86.basic x86proved.x86.program.
Require Import x86proved.x86.call x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.inlinealloc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Fixpoint listSeg (p e:DWORD) (vs: seq DWORD) :SPred :=
  if vs is v::vs
  then Exists q, p :-> v ** p +#4 :-> q ** listSeg q e vs
  else p == e /\\ empSP.

Definition inlineHead_spec (r1 r2:Reg) (i j p e: DWORD) v vs (instrs: program) :=
  |-- 
  (safe @ (EIP ~= j ** r1~=v) -->>
   safe @ (EIP ~= i ** r1?)) @
  (listSeg p e (v::vs) ** r2~=p) <@ (i -- j :-> instrs).
Implicit Arguments inlineHead_spec [].

Definition inlineTail_spec (r1 r2:Reg) (i j p e: DWORD) v vs (instrs: program) :=
  |-- 
  (safe @ (Exists q, EIP ~= j ** r1~=q ** listSeg p q (v::nil) ** listSeg q e vs) -->>
   safe @ (EIP ~= i ** r1? ** listSeg p e (v::vs))) @
  (r2~=p) <@ (i -- j :-> instrs).
Implicit Arguments inlineTail_spec [].

(* Head is in EAX, tail is in EDI, result in EDI, ESI trashed *)
Definition inlineCons_spec (r1 r2:Reg) heapInfo (failLabel:DWORD) (i j h t e: DWORD) vs (instrs: program):=
  |-- (
      safe @ (EIP ~= failLabel ** r1? ** r2? ** EDI?) //\\
      safe @ (EIP ~= j ** Exists pb, r1? ** r2? ** EDI ~= pb ** listSeg pb t [::h])
    -->>
      safe @ (EIP ~= i ** r1~=h ** r2~=t ** EDI?)
    ) @
    (ESI? ** OSZCP? ** allocInv heapInfo ** listSeg t e vs)
    <@ (i -- j :-> instrs).

Definition callCons_spec (r1 r2: Reg) heapInfo (i j h t e: DWORD) vs (instrs: program):=
  (toyfun i (r1~=h ** r2~=t ** EDI?) 
            (r1? ** r2? ** (EDI ~= #0 \\// (Exists pb, EDI ~= pb ** listSeg pb t [::h])))) @
  (ESI? ** OSZCP? ** allocInv heapInfo ** listSeg t e vs)
  <@ (i -- j :-> mkbody_toyfun instrs).
