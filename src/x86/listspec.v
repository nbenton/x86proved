(*===========================================================================
  Lists
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.safe x86proved.x86.basic x86proved.x86.program.
Require Import x86proved.x86.call x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor x86proved.x86.inlinealloc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Fixpoint listSeg (p e:ADDR) (vs: seq QWORD) :SPred :=
  if vs is v::vs
  then Exists q:ADDR, p :-> v ** (p +#8) :-> q ** listSeg q e vs
  else p == e /\\ empSP.

Definition inlineHead_spec (r1 r2:GPReg64) (p e: ADDR) v vs (instrs: program) :=
  |-- basic r1? instrs (r1~=v) @ (listSeg p e (v::vs) ** r2~=p).
Implicit Arguments inlineHead_spec [].

Definition inlineTail_spec (r1 r2:GPReg64) (p e: ADDR) v vs (instrs: program) :=
  |-- basic (r1? ** listSeg p e (v::vs)) instrs
            (Exists q, r1~=q ** listSeg p q (v::nil) ** listSeg q e vs) @ (r2~=p). 
Implicit Arguments inlineTail_spec [].

(* Head is in RAX, tail is in RDI, result in RDI *)
Definition inlineCons_spec (r1 r2:GPReg64) (failLabel:ADDR) (i j h t e: ADDR) vs (instrs: program):=
  |-- (
      safe @ (UIP ~= failLabel ** r1? ** r2? ** RDI?) //\\
      safe @ (UIP ~= j ** Exists pb, r1? ** r2? ** RDI ~= pb ** listSeg pb t [::h])
    -->>
      safe @ (UIP ~= i ** r1~=h ** r2~=t ** RDI?)
    ) @
    (OSZCP? ** allocInv ** listSeg t e vs)
    c@ (i -- j :-> instrs).

Definition callCons_spec (r1 r2: GPReg64) (i j h t e: ADDR) vs (instrs: program):=
  (toyfun i (r1~=h ** r2~=t ** RDI?) 
            (r1? ** r2? ** (RDI ~= #0 \\// (Exists pb, RDI ~= pb ** listSeg pb t [::h])))) @
  (OSZCP? ** allocInv ** listSeg t e vs)
  c@ (i -- j :-> mkbody_toyfun instrs).
