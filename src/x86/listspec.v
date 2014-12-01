(*===========================================================================
  Lists
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.opred x86proved.obs x86proved.x86.basic x86proved.x86.program.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor x86proved.x86.inlinealloc x86proved.x86.call.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Fixpoint listSeg (p e:ADDR) (vs: seq QWORD) :SPred :=
  if vs is v::vs
  then Exists q:ADDR, p :-> v ** (p +#8) :-> q ** listSeg q e vs
  else p == e /\\ empSP.

Definition inlineHead_spec (r1 r2:GPReg64) (i j:ADDR) (p e: QWORD) v vs (instrs: program) :=
  |-- Forall O : OPred,
  (obs O @ (UIP ~= j ** r1~=v) -->>
   obs O @ (UIP ~= i ** r1?)) @
  (listSeg p e (v::vs) ** r2~=p) <@ (i -- j :-> instrs).
Implicit Arguments inlineHead_spec [].

Definition inlineTail_spec (r1 r2:GPReg64) (i j:ADDR) (p e: QWORD) v vs (instrs: program) :=
  |-- Forall O : OPred,
  (obs O @ (Exists q, UIP ~= j ** r1~=q ** listSeg p q (v::nil) ** listSeg q e vs) -->>
   obs O @ (UIP ~= i ** r1? ** listSeg p e (v::vs))) @
  (r2~=p) <@ (i -- j :-> instrs).
Implicit Arguments inlineTail_spec [].

(* Head is in RAX, tail is in RDI, result in RDI *)
Definition inlineCons_spec (r1 r2:GPReg64) (failLabel i j:ADDR) (h t e: QWORD) vs (instrs: program):=
  |-- Forall O : OPred, (
      obs O @ (UIP ~= failLabel ** r1? ** r2? ** RDI?) //\\
      obs O @ (UIP ~= j ** Exists pb, r1? ** r2? ** RDI ~= pb ** listSeg pb t [::h])
    -->>
      obs O @ (UIP ~= i ** r1~=h ** r2~=t ** RDI?)
    ) @
    (OSZCP? ** allocInv ** listSeg t e vs)
    <@ (i -- j :-> instrs).


Definition callCons_spec (r1 r2: GPReg64) (i j h t e: ADDR) vs (instrs: program):=
  (toyfun i (r1~=h ** r2~=t ** RDI?) empOP
            (r1? ** r2? ** (RDI ~= #0 \\// (Exists pb, RDI ~= pb ** listSeg pb t [::h])))) @
  (OSZCP? ** allocInv ** listSeg t e vs)
  <@ (i -- j :-> mkbody_toyfun instrs).

