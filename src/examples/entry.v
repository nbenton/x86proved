Require Import Ssreflect.ssreflect Ssreflect.seq Ssreflect.finfun Ssreflect.tuple Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.x86.mem x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec.
Require Import x86proved.x86.program x86proved.x86.macros Coq.Strings.Ascii.

Local Open Scope instr_scope.

Definition sumEx :=
  LOCAL loopBody;
      MOV EAX, (1:DWORD);;
      MOV EBX, (10:DWORD);;
      XOR ECX, ECX;;
    loopBody:;;
      ADD ECX, EAX;;
      INC EAX;;
      CMP EAX, EBX;;
      JNZ loopBody
  .

Definition outEx :=
  LOCAL loopBody;
      MOV EAX, (1:DWORD);;
      MOV EBX, (10:DWORD);;
      XOR ECX, ECX;;
    loopBody:;;
      OUT 50, AL;;
      INC EAX;;
      CMP EAX, EBX;;
      JNZ loopBody
  .

Definition screenAddr:DWORD := #x"000b8000" +# 160*32.

Definition simpleScreenEx :=
  LOCAL busyBody;
    busyBody:;;
      MOV EDI, screenAddr;;
      MOV BYTE PTR [EDI], (#(nat_of_ascii "D"):BYTE);;
      MOV BYTE PTR [EDI+1], (#63:BYTE);;
      JMP busyBody
  .

Definition prettyEx :=
  LOCAL loopBody;
  LOCAL busyBody;
      MOV EDI, screenAddr;;
      MOV EAX, (31:DWORD);;
      MOV EBX, (255:DWORD);;
    loopBody:;;
      MOV BYTE PTR [EDI], (#1:BYTE);;
      INC EDI;;
      MOV BYTE PTR [EDI], AL;;
      INC EDI;;
      ADD EAX, (16:DWORD);;
      CMP EAX, EBX;;
      JNZ loopBody;;
    busyBody:;;
      JMP busyBody
  .
