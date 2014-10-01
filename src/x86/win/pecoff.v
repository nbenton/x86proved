(*===========================================================================
  PE/COFF generation

  We expect the following information:

  * imageBase:DWORD
    The location at which the image should be loaded

  * imports: seq DLLImports
    For each DLL that's imported, its name and a sequence of import entries

  * data: program
    Assembles to produce a data section with no reference to code.

  * code: DWORD -> seq (seq DWORD) -> program
    Given the base address of the data section, and addresses for each of the imports,
    produce the code section.

  From data we calculate the size (exact, and rounded up to page size, call it D)
  We place the data at RVA 0x1000, and the code at RVA D+0x1000. Entry point is
  assumed to coincide with the start of the code.

  Currently we emit an executable with three sections (code, data and imports), but with
  no exports or base relocations.
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program x86proved.x86.programassem x86proved.cursor.
Require Import Coq.Strings.Ascii Coq.Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive TargetType :=
| DLL
| EXE
.

Inductive ImportEntry :=
| ImportByOrdinal of nat
| ImportByName of string.

Record DLLImport := {
  DLLImport_name: string;
  DLLImport_entries: seq ImportEntry
}.

Record DLLExport := {
  DLLExport_name: string;
  DLLExport_VA: QWORD
}.

(*
(* We need character, string and byte sequence writers *)
Instance charWriter : Writer ascii :=
  fun c => writeBYTE (nat_of_ascii c).

Instance stringWriter : Writer string :=
  fix sw s :=
    if s is String c s
    then do! writeNext c; sw s
    else retn tt.

Infix "||" := orB.
Infix "&&" := andB.

(* Section 2.1: MSDOS Stub *)
(* This is the minimal stub taken from the "Tiny PE" *)
Require Import Ssreflect.ssralg.
Definition MSDOSStub: program :=
LOCAL START; LOCAL END;
START:;;
  ds "MZ"%string;;
  pad 58;;
  dd (low 32 (END - START))%R;;
END:;.

(* Section 2.2: Signature *)
Definition PEsig:program :=
  ds "PE"%string;;
  dw 0.

(* Section 2.3: COFF File Header *)
Definition makeCOFFFileHeader
  (Machine: WORD)
  (NumberOfSections: nat)
  (TimeDateStamp: DWORD)
  (PointerToSymbolTable: DWORD)
  (NumberOfSymbols: nat)
  (SizeOfOptionalHeader: WORD)
  (Characteristics: WORD) : program :=

  dw Machine;;
  dw NumberOfSections;;
  dd TimeDateStamp;;
  dd PointerToSymbolTable;;
  dd NumberOfSymbols;;
  dw SizeOfOptionalHeader;;
  dw Characteristics.

(* Section 2.3.1: Machine types *)
Definition IMAGE_FILE_MACHINE_i386 := #x"014c".

(* Section 2.3.2: Characteristics. We omit deprecated flags *)
Definition IMAGE_FILE_RELOCS_STRIPPED     := #x"0001".
Definition IMAGE_FILE_EXECUTABLE_IMAGE    := #x"0002".
Definition IMAGE_FILE_LARGE_ADDRESS_AWARE := #x"0020".
Definition IMAGE_FILE_32BIT_MACHINE       := #x"0100".
Definition IMAGE_FILE_DEBUG_STRIPPED      := #x"0200".
Definition IMAGE_FILE_SYSTEM              := #x"1000".
Definition IMAGE_FILE_DLL                 := #x"2000".
Definition IMAGE_FILE_UP_SYSTEM_ONLY      := #x"4000".

(* Windows Subsystem *)
Definition IMAGE_SUBSYSTEM_NATIVE := 1.
Definition IMAGE_SUBSYSTEM_WINDOWS_GUI := 2.
Definition IMAGE_SUBSYSTEM_WINDOWS_CUI := 3.

(* DLL Characteristics *)
Definition IMAGE_DLL_CHARACTERISTICS_DYNAMIC_BASE    := #x"0040".
Definition IMAGE_DLL_CHARACTERISTICS_FORCE_INTEGRITY := #x"0080".
Definition IMAGE_DLL_CHARACTERISTICS_NX_COMPAT       := #x"0100".
Definition IMAGE_DLL_CHARACTERISTICS_NO_ISOLATION    := #x"0200".
Definition IMAGE_DLL_CHARACTERISTICS_NO_SEH          := #x"0400".
Definition IMAGE_DLL_CHARACTERISTICS_NO_BIND         := #x"0800".
Definition IMAGE_DLL_CHARACTERISTICS_TERMINAL_SERVER_AWARE := #x"8000".

Definition makeMinimalHeader (targetType : TargetType) numberOfSections opthdrsize :=
  makeCOFFFileHeader
    IMAGE_FILE_MACHINE_i386
    numberOfSections (* Number of sections *)
    0             (* Timestamp *)
    0             (* Symbol table *)
    0              (* Number of symbols *)
    opthdrsize     (* Size of optional header *)
    (IMAGE_FILE_32BIT_MACHINE ||
     IMAGE_FILE_EXECUTABLE_IMAGE || (* this is needed for DLLs too *)
     (if targetType is DLL then IMAGE_FILE_DLL else #x"0000") ||
     IMAGE_FILE_RELOCS_STRIPPED)
    .

Record Version := {majorVersion: WORD;
                   minorVersion: WORD}.
Instance writeVersion: Writer Version := fun v =>
  do! writeNext (majorVersion v); writeNext (minorVersion v).

Definition dv (v: Version) : program :=
  dw (majorVersion v);;
  dw (minorVersion v).

(* Alignment within the file can be on 512 byte boundaries *)
(* But this doesn't work yet because the assembler needs the file
   to match the memory layout *)
Definition fileAlignBits := 9.
Definition fileAlign: DWORD := iter fileAlignBits shlB 1.

(* Once mapped into memory the sections must be on 4K boundaries *)
Definition sectAlignBits := 12.
Definition sectAlign: DWORD := iter sectAlignBits shlB 1.

Fixpoint fixedString n s :=
  match n, s with
  | 0, _ => prog_skip
  | n.+1, EmptyString => db 0;; fixedString n s
  | n.+1, String c s => db (fromNat (nat_of_ascii c));; fixedString n s
  end.

(* Section 3: Section header. We truncate/zero-pad the string to 8 characters *)
Definition makeSectionHeader
  (Name: string)              (* Will be truncated and zero-padded to 8 characters *)
  (VirtualSize: DWORD)        (* Size when loaded into memory; can be greater than raw size *)
  (VirtualAddress: DWORD)     (* Address when loaded into memory *)
  (SizeOfRawData: DWORD)      (* Actual size in the file. Must be multiple of FileAlignment *)
  (PointerToRawData: DWORD)   (* Address in the file. Must  be multiple of FileAlignment *)
  (PointerToRelocations PointerToLinenumbers: DWORD)  (* Zero for executable images *)
  (NumberOfRelocations NumberOfLinenumbers: WORD)     (* Zero for executable images *)
  (Characteristics: DWORD) :=                         (* Section Flags *)

  fixedString 8 Name;;
  dd VirtualSize;;
  dd VirtualAddress;;
  dd SizeOfRawData;;
  dd PointerToRawData;;
  dd PointerToRelocations;;
  dd PointerToLinenumbers;;
  dw NumberOfRelocations;;
  dw NumberOfLinenumbers;;
  dd Characteristics.

(* Section 3.1: Section Flags *)
Definition IMAGE_SCN_CNT_CODE               := #x"00000020".
Definition IMAGE_SCN_CNT_INITIALIZED_DATA   := #x"00000040".
Definition IMAGE_SCN_CNT_UNINITIALIZED_DATA := #x"00000080".
Definition IMAGE_SCN_MEM_DISCARDABLE        := #x"02000000".
Definition IMAGE_SCN_MEM_NOT_CACHED         := #x"04000000".
Definition IMAGE_SCN_MEM_NOT_PAGED          := #x"08000000".
Definition IMAGE_SCN_MEM_SHARED             := #x"10000000".
Definition IMAGE_SCN_MEM_EXECUTE            := #x"20000000".
Definition IMAGE_SCN_MEM_READ               := #x"40000000".
Definition IMAGE_SCN_MEM_WRITE              := #x"80000000".

(*=section *)
Inductive section :=
  mkSection (name: string) (characteristics: DWORD) (content: program).
(*=End *)

(*=mkCodeSection *)
Definition CODE :=
  mkSection ".text" (IMAGE_SCN_CNT_CODE ||
                     IMAGE_SCN_MEM_EXECUTE || IMAGE_SCN_MEM_READ).
(*=End *)
Definition RDATA :=
  mkSection ".rdata" (IMAGE_SCN_CNT_INITIALIZED_DATA ||
                      IMAGE_SCN_MEM_READ).
(*=mkDataSection *)
Definition DATA :=
  mkSection ".data" (IMAGE_SCN_CNT_INITIALIZED_DATA ||
                     IMAGE_SCN_MEM_READ || IMAGE_SCN_MEM_WRITE).
(*=End *)

Definition EDATA :=
  mkSection ".edata"
  (IMAGE_SCN_CNT_INITIALIZED_DATA || IMAGE_SCN_MEM_READ || IMAGE_SCN_MEM_WRITE).

Definition IDATA :=
  mkSection ".idata"
  (IMAGE_SCN_CNT_INITIALIZED_DATA || IMAGE_SCN_MEM_READ || IMAGE_SCN_MEM_WRITE).

(* s is a program that when assembled produces the unaligned section *)
Fixpoint makeSections dRVA (pointerToRawData:DWORD) endHeaders (sections: seq section)
  (headers bodies: seq program)
  (codeStart dataStart SizeOfCode SizeOfInitializedData SizeOfUninitializedData:DWORD)
  makePrefix : program :=
  (if sections is mkSection Name characteristics contents :: sections
  then
    LOCAL sectionStart; LOCAL rawEnd; LOCAL inFileEnd; LOCAL inMemoryEnd;
    let: rawSize := low 32 (rawEnd - sectionStart) in
    let: virtualSize := low 32 (inMemoryEnd - sectionStart) in
    let: sizeOfRawData := low 32 (inFileEnd - sectionStart) in
    let: isCode := (characteristics && IMAGE_SCN_CNT_CODE) != #0 in
    let: isData := (characteristics && IMAGE_SCN_CNT_INITIALIZED_DATA) != #0 in
    let: isUninitializedData := (characteristics && IMAGE_SCN_CNT_UNINITIALIZED_DATA) != #0 in
    makeSections
     dRVA (pointerToRawData + sizeOfRawData)
     endHeaders
     sections
      (
        (fixedString 8 Name;;
        dd rawSize;;
        dRVA sectionStart;;
        dd sizeOfRawData;;
        dd pointerToRawData;;
        dd 0;; (* PointerToRelocations *)
        dd 0;; (* PointerToLinenumbers *)
        dw 0;; (* NumberOfRelocations *)
        dw 0;; (* NumberOfLinenumbers *)
        dd characteristics) ::
        headers
      )

      ((align fileAlignBits;; skipAlign sectAlignBits;;
       sectionStart:;; contents;;
      rawEnd:;; align fileAlignBits;;
      inFileEnd:;; skipAlign sectAlignBits;;
      inMemoryEnd:;)::bodies)
      (if (codeStart == #0) && isCode then low 32 sectionStart else codeStart)
      (if (dataStart == #0) && isData then low 32 sectionStart else dataStart)
      (if isCode then SizeOfCode + low 32 (inFileEnd - sectionStart)
       else SizeOfCode)
      (if isData then SizeOfInitializedData + low 32 (inFileEnd - sectionStart)
       else SizeOfInitializedData)
      (if isUninitializedData then SizeOfUninitializedData + low 32 (inFileEnd - sectionStart)
       else SizeOfUninitializedData)
      makePrefix
  else
    makePrefix codeStart dataStart SizeOfCode SizeOfInitializedData SizeOfUninitializedData;;
    foldr (fun p1 p2 => p2;;p1) prog_skip headers;;
    align fileAlignBits;;
    endHeaders:;;
    foldr (fun p1 p2 => p2;;p1) prog_skip bodies)%R.


Fixpoint makeString (s:string) :=
  if s is String c s
  then db (nat_of_ascii c);; makeString s
  else db 0.

(* [kEAT] is the continuation program writing the beginning of the Export Address Table
   [kENPT] is the continuation program writing the beginning of the Export Name Pointer Table
   [kEOT] is the continuation program writing the beginning of the Export Ordinal Table
   The last 2 tables are built in reverse order so that name addresses appear in lexical order in the
   Export Name Pointer Table.
 *)
Fixpoint computeExportTables (dRVA:QWORD -> program) (exports: seq DLLExport) baseEAT baseENPT baseEOT (kEAT kENPT kEOT : program) (ord : WORD) : program :=
  (if exports is Build_DLLExport name addr :: exports
  then
    LOCAL NAME;
    computeExportTables
      dRVA exports baseEAT baseENPT baseEOT
      (kEAT ;; dRVA addr)
      (dRVA NAME;; kENPT)
      (dw ord ;; kEOT)
      (ord + 1);;
    NAME:;;
    makeString name
  else
  baseEAT:;;
    kEAT ;;
  baseENPT:;;
    kENPT;;
  baseEOT:;;
    kEOT)%R.

Definition makeExportTables dRVA (exports : seq DLLExport) baseEAT baseENPT baseEOT :=
  computeExportTables dRVA exports baseEAT baseENPT baseEOT prog_skip prog_skip prog_skip
  (* the next field should be set to the ordinal base, according to what's shown
     in the example in the section 5.3 of the spec. However, in reality, tools
     seem to agree that this is #0-based.
     See: http://stackoverflow.com/questions/5653316
   *)
  #0
.

Definition makeExportDirectoryTable (dRVA:QWORD -> program) (nbEntries baseName baseEAT baseENPT baseEOT : DWORD) :=
  dd 0;; (* Reserved *)
  dd 0;; (* Time stamp *)
  dw 0;; (* Major version *)
  dw 0;; (* Minor version *)
  dRVA baseName;; (* Name RVA *)
  dd 1;; (* Ordinal base *)
  dd nbEntries;; (* # of entries in Address Table *)
  dd nbEntries;; (* # of entries in Name Pointer and Ordinal Tables *)
  dRVA baseEAT;; (* EAT RVA *)
  dRVA baseENPT;; (* NPT RVA *)
  dRVA baseEOT  (* OT RVA *)
  .


(* We lay out the .idata section as follows.

     IAT (One DWORD per entry, with null at end, for each DLL)
     ILT (Exactly the same as the IAT)
     Import directory (5 DWORDs per DLL, with 5 nulls at the end)
     Strings

  NOTE: the IAT and ILT must be DWORD-aligned. This is not mentioned in the PE/COFF spec!
*)
Fixpoint makeIATsILTs (dRVA:QWORD -> program) (imports: seq (QWORD*(QWORD*DLLImport))) (importAddrs: seq (seq QWORD)) (IATs ILTs: program) :=
  match imports, importAddrs with
   (IATbase,(ILTbase,Build_DLLImport _ entries))::imports, addrs::importAddrs =>
    (fix computeIATandILTforOneDLL (entries: seq ImportEntry) (addrs: seq QWORD) (IAT ILT: program) : program :=
       match entries, addrs with
       | entry::entries, addr::addrs =>
         match entry with
         | ImportByOrdinal n =>
           computeIATandILTforOneDLL entries addrs
             (IAT;; dd (#x"80000000" || #n))
             (ILT;; dd (#x"80000000" || #n))

         | ImportByName n =>
           LOCAL NAME;
             computeIATandILTforOneDLL entries addrs (IAT;; addr:;; dRVA NAME) (ILT;; dRVA NAME);;
           NAME:;;
             dw 0;; (* hint *)
             makeString n;;
             align 1 (* align on even byte *)
         end
       | _, _ => makeIATsILTs dRVA imports importAddrs (IAT;; dd 0) (ILT;; dd 0)
      end
    ) entries addrs (IATs;; align 2;; IATbase:;) (ILTs;; align 2;; ILTbase:;)
  | _, _ => IATs;; ILTs
  end.

Fixpoint attachLOCALS T (xs: seq T) k :=
  if xs is x::xs' then LOCAL L; attachLOCALS xs' (fun ys => k ((L,x)::ys))
  else k nil.

Fixpoint makeImportDirectory (dRVA:QWORD -> program) (imports: seq (QWORD*(QWORD*DLLImport))) endIDT :=
  if imports is (IAT,(ILT,Build_DLLImport name entries))::imports
  then
    LOCAL NAME;
      dRVA ILT;;  (* ILT RVA *)
      dd 0;;     (* Time stamp *)
      dd 0;;     (* Forwarder chain *)
      dRVA NAME;; (* Name RVA *)
      dRVA IAT;;  (* IAT RVA *)
      makeImportDirectory dRVA imports endIDT;;
    NAME:;;
      makeString name
  else
  (* The table must end with an empty entry *)
    dd 0;; dd 0;; dd 0;; dd 0;; dd 0;;
    endIDT:;.

Open Scope instr_scope. Open Scope ring_scope.
Definition makePEfile
  (dRVA: QWORD -> program)
  targetType                               (* Target type: EXE or DLL *)
  entryPoint                               (* Entry point for execution, #0 if not present *)
  (exportTableStart exportTableEnd
  importTableStart importTableEnd
  IATStart IATEnd : DWORD)
  (sections: seq section) :=
LOCAL imageBase;
LOCAL startDirectories; LOCAL endHeaders; LOCAL endFile;
LOCAL startOptionalHeader; LOCAL endOptionalHeader;
imageBase:;;
  MSDOSStub;;
  PEsig;;
  makeMinimalHeader targetType (size sections) (low 16 (endOptionalHeader - startOptionalHeader));;
  makeSections dRVA fileAlign endHeaders sections nil nil 0 0 0 0 0
  (fun BaseOfCode BaseOfData SizeOfCode SizeOfInitializedData SizeOfUninitializedData =>
startOptionalHeader:;;
  dw #x"010B";;    (* PE32 format *)
  db 11;; db 0;; (* linker version, major & minor numbers *)
  dd SizeOfCode;;
  dd SizeOfInitializedData;;
  dd SizeOfUninitializedData;;
  dRVA (if entryPoint == #0 then if targetType is EXE then BaseOfCode else #0 else entryPoint);;
  dRVA BaseOfCode;;
  dRVA BaseOfData;;
  dd (low 32 imageBase);;
  dd sectAlign;;                (* SectionAlignment *)
  dd fileAlign;;                (* FileAlignment *)
  dv (Build_Version 6 0);;      (* OperatingSystemVersion *)
  dv (Build_Version 0 0);;      (* ImageVersion *)
  dv (Build_Version 6 0);;      (* SubsystemVersion *)
  dd 0;;                        (* Win32VersionValue, must be zero *)
  dd (low 32(endFile - imageBase));;    (* SizeOfImage *)
  dd (low 32 (endHeaders - imageBase));; (* SizeOfHeaders *)
  dd 0;;                        (* CheckSum *)
  dw IMAGE_SUBSYSTEM_WINDOWS_CUI;;(* Subsystem *)
  dw (IMAGE_DLL_CHARACTERISTICS_NO_SEH ||
     IMAGE_DLL_CHARACTERISTICS_NX_COMPAT ||
     if targetType is DLL then IMAGE_DLL_CHARACTERISTICS_DYNAMIC_BASE else #x"0000");; (* DllCharacteristics *)
  dd #x"00100000";;               (* SizeOfStackReserve *)
  dd #x"00001000";;               (* SizeOfStackCommit *)
  dd #x"00100000";;               (* SizeOfHeapReserve *)
  dd #x"00001000";;               (* SizeOfHeapCommit *)
  dd 0;;                          (* LoaderFlags, must be zero *)
  dd 16;;                         (* NumberOfRvaAndSizes *)
startDirectories:;;
  (* Exports *)
  dRVA exportTableStart;; dd (exportTableEnd - exportTableStart);;
  (* Imports *)
  dRVA importTableStart;; dd (importTableEnd - importTableStart);;
  (* Resources *)
  dd 0;; dd 0;;
  (* Exceptions *)
  dd 0;; dd 0;;
  (* Certificates *)
  dd 0;; dd 0;;
  (* Base relocations *)
  dd 0;; dd 0;;
  (* Debug *)
  dd 0;; dd 0;;
  (* Architecture *)
  dd 0;; dd 0;;
  (* Global Ptr *)
  dd 0;; dd 0;;
  (* TLS Table *)
  dd 0;; dd 0;;
  (* Load Config *)
  dd 0;; dd 0;;
  (* Bound Import *)
  dd 0;; dd 0;;
  (* IAT *)
  dRVA IATStart;; dd (IATEnd - IATStart);;
  (* Delay Import Descriptor *)
  dd 0;; dd 0;;
  (* CLR Runtime Header *)
  dd 0;; dd 0;;
  (* Reserved *)
  dd 0;; dd 0;;
endOptionalHeader:;)
;;
endFile:;.

Definition makeExportSection (dRVA:QWORD -> program) startEDT endEDT progName exports :=
  LOCAL baseEAT; LOCAL baseENPT; LOCAL baseEOT; LOCAL baseName;
baseName:;;
  makeString progName;;
  align 2;;
  makeExportTables dRVA exports baseEAT baseENPT baseEOT
;;
  align 2;;
  startEDT:;;
  makeExportDirectoryTable
     dRVA
     (size exports)
     (low 32 baseName)
     (low 32 baseEAT)
     (low 32 baseENPT)
     (low 32 baseEOT);;
  endEDT:;
  .

Definition makeImportSection dRVA startIDT endIDT imports (importAddrs: seq (seq QWORD)) :=
  (* Labels for IATs *)
  attachLOCALS imports (fun imports1 =>
  (* Labels for ILTs *)
  attachLOCALS imports1 (fun imports2 =>
  align 2;;
  startIDT:;;
  (* Make import directory, with RVAs into IATs and ILTs *)
  makeImportDirectory dRVA imports2 endIDT;;
  (* Make IATs and ILTs themselves *)
  makeIATsILTs dRVA imports2 importAddrs prog_skip prog_skip)).

(* Top-level program *)
(* Consists of a sequence of
     - DLL import, followed by a sequence of imports by symbol; or
     - global label declaration, shared between sections, and optionally exported as a string;
     - entry point label declaration
   followed by a sequence of *sections*.
*)
(*=topprog *)
Inductive topprog :=
| topprog_global (name: option string) (t: QWORD -> topprog)
| topprog_importdll (name: string) (p: topimps)
| topprog_entry (t: QWORD -> topprog)
| topprog_sect (sect: section) (t: topprog)
| topprog_end
with topimps :=
| topimps_import (name: string) (t: QWORD -> topimps)
| topimps_topprog (t: topprog).

Coercion topimps_topprog : topprog >-> topimps.

Fixpoint applyTopProg {T} (local: (QWORD -> T) -> T) k (imports: seq DLLImport) (importAddrs: seq (seq QWORD))
  (exports: seq DLLExport) (sections: seq section) (entry:QWORD) t : T :=
  match t with
  | topprog_sect s t =>
    applyTopProg local k imports importAddrs exports (s :: sections) entry t

  | topprog_end =>
    k (rev imports) (rev importAddrs) exports (rev sections) entry

  | topprog_entry f =>
    local (fun L =>
    applyTopProg local k imports importAddrs exports sections L (f L))

  | topprog_importdll name t =>
    applyTopImps local k name nil nil imports importAddrs exports sections entry t

  | topprog_global (Some name) t =>
    local (fun L =>
    applyTopProg local k imports importAddrs (Build_DLLExport name L::exports) sections entry (t L))

  | topprog_global None t =>
    local (fun L =>
    applyTopProg local k imports importAddrs exports sections entry (t L))
  end

with applyTopImps {T} (local : (QWORD -> T) -> T) k nameDLL entries addrs imports importAddrs exports sections entry (t: topimps) :=
  match t with
  | topimps_import name t =>
    local (fun L => applyTopImps local k nameDLL
    (ImportByName name::entries) (L::addrs) imports importAddrs exports sections entry (t L))

  | topimps_topprog t =>
    applyTopProg local k (Build_DLLImport nameDLL (rev entries)::imports) (rev addrs::importAddrs)
      exports sections entry t
  end.

Definition applyClosedTopProg {T} local k := applyTopProg (T:=T) local k nil nil nil nil 0.

Notation "'IMPORTDLL' s ';' p" := (topprog_importdll s p)
  (at level 65, right associativity).
Notation "'IMPORT' s 'as' l ';' p" := (topimps_import s (fun l => p))
  (at level 65, l ident, right associativity).
Notation "'GLOBAL' l 'as' s ';' p" := (topprog_global (Some s) (fun l => p))
  (at level 65, l ident, right associativity).
Notation "'GLOBAL' l ';' p" := (topprog_global None (fun l => p))
  (at level 65, l ident, right associativity).
Notation "'ENTRY' l ';' p" := (topprog_entry (fun l => p))
  (at level 65, l ident, right associativity).
Notation "'SECTION' s p ';' t" := (topprog_sect (s p) t)
  (at level 66, s at level 0, p at next level, right associativity).
Notation "'SECTION' s p" := (topprog_sect (s p) topprog_end)
  (at level 66, s at level 0, p at next level, right associativity).
(*=End *)

(* Given a base address for the IAT and a top-level program, produce a program,
   a sequence of DLLImport structures and, an export list *)
(*
Fixpoint computeImports (t: topprog)
  (imports: seq DLLImport) (importAddrs: seq (seq DWORD)) (exports: seq DLLExport) (sections: seq section)
  entry k :=
  match t with
  | topprog_end =>
    k (rev imports) (rev importAddrs) exports (rev sections) entry

  | topprog_sect s t =>
    computeImports t imports importAddrs exports (s :: sections) entry k

  | topprog_importdll name t => computeImportsOneDLL t name nil nil imports importAddrs exports sections entry k
  | topprog_global (Some name) t =>
    LOCAL L;
    computeImports (t L) imports importAddrs (Build_DLLExport name L::exports) sections entry k
  | topprog_global None f =>
    LOCAL L;
    computeImports (f L) imports importAddrs exports sections entry k
  | topprog_entry f =>
    LOCAL L;
    computeImports (f L) imports importAddrs exports sections L k
  end
with computeImportsOneDLL (t: topimps) nameDLL entries addrs imports importAddrs exports sections entry k :=
  match t with
  | topimps_import name f =>
    LOCAL L; computeImportsOneDLL (f L) nameDLL
                         (ImportByName name::entries) (L::addrs) imports importAddrs exports sections entry k
  | topimps_topprog t =>
    computeImports t (Build_DLLImport nameDLL (rev entries)::imports) (rev addrs::importAddrs) exports sections entry k
  end.
*)

Definition makeRange X (xs: seq X) f :=
  if xs is _::_ then LOCAL startLabel; LOCAL endLabel; f startLabel endLabel
  else f 0 0.

(*=computeRVAsIn *)
Definition computeRVAsIn (f: (QWORD -> program) -> program) : program :=
  LOCAL base;
  base:;;
    f (fun VA => dd (if VA == #0 then #0 else VA - base)).
(*=End *)

Require Import x86proved.pointsto x86proved.spred x86proved.septac.
Lemma computeRVAsIn_interp (k: (DWORD -> program) -> program) (i:DWORD) j :
  interpProgram i j
  (k (fun VA => dd (if VA == #0 then #0 else VA - i)))
  |-- interpProgram i j (computeRVAsIn k).
Proof. simpl. apply lexistsR with i. apply lexistsR with i. sbazooka. Qed.

Lemma MSDOSStubHasSize : hasSize 64 MSDOSStub.
Proof. rewrite /MSDOSStub.
apply localHasSize => L1.
apply localHasSize => L2.
apply (seqHasSize (n1:=0)). apply labelHasSize.
apply (seqHasSize (n1:=2)). apply dsHasSize.
apply (seqHasSize (n1:=58)). apply padHasSize.
apply (seqHasSize (n1:=4)). apply ddHasSize.
apply labelHasSize.
Qed.

Lemma PESigHasSize : hasSize 4 PEsig.
Proof. rewrite /PEsig.
apply (seqHasSize (n1:=2)). apply dsHasSize.
apply dwHasSize.
Qed.

Lemma MSDOSStubAprt p q : p -- q :-> MSDOSStub |-- apart 64 p q /\\ p -- q :-> MSDOSStub.
Proof. apply MSDOSStubHasSize. Qed.

Lemma makeMinimalHeader_interp (i:DWORD) j  targetType numberOfSections opthdrsize :
  i -- j :-> makeMinimalHeader targetType numberOfSections opthdrsize
  |-- Exists i1, Exists i2, memAny i i1 ** i1 -- i2 :-> (numberOfSections:WORD) ** memAny i2 j.
Proof. rewrite /makeMinimalHeader/makeCOFFFileHeader. unfold_program.
sdestructs => i1 i2 i3 i4 i5 i6.
rewrite -> programMemIs_entails_memAny.
rewrite programMemIsData.
repeat rewrite -> programMemIs_entails_memAny.
repeat rewrite -> memAnyMerge.
sbazooka.
Qed.

Lemma makePEfile_interp (i:DWORD) j
  dRVA targetType entryPoint exportTableStart exportTableEnd
  importTableStart importTableEnd IATStart IATEnd sections :

  i -- j :->
  makePEfile
    dRVA
    targetType entryPoint
    exportTableStart exportTableEnd
   importTableStart importTableEnd
    IATStart IATEnd sections
  |-- Exists i1, Exists i2, memAny i i1 ** i1 -- i2 :-> (size sections:WORD) ** memAny i2 j.
Proof. rewrite /makePEfile.
rewrite -> programMemIsLocal. sdestructs => L1.
rewrite -> programMemIsLocal. sdestructs => L2.
rewrite -> programMemIsLocal. sdestructs => L3.
rewrite -> programMemIsLocal. sdestructs => L4.
rewrite -> programMemIsLocal. sdestructs => L5.
rewrite -> programMemIsLocal. sdestructs => L6.
rewrite -> programMemIsSeq. sdestructs => L7.
rewrite -> programMemIsSeq. sdestructs => L8.
rewrite -> programMemIsSeq. sdestructs => L9.
rewrite -> programMemIsSeq. sdestructs => L10.
rewrite -> makeMinimalHeader_interp.
repeat rewrite -> programMemIs_entails_memAny.
repeat rewrite -> memAnyMerge.
sdestructs => i1 i2.
apply lexistsR with i1. apply lexistsR with i2. ssimpl.
(* Need some tactic to do merging modulo AC! *)
rewrite -sepSPA.
rewrite -> memAnyMerge.
rewrite -sepSPA.
rewrite -> memAnyMerge.
rewrite sepSPA.
rewrite -> memAnyMerge.
rewrite -sepSPA.
rewrite -> memAnyMerge.
sbazooka.
Qed.

Definition makePEfile_program
  (targetType: TargetType) (progName: string) (t: topprog) : program :=
  computeRVAsIn (fun dRVA =>
  applyClosedTopProg prog_declabel
  (fun imports importAddrs exports sections entry =>

  makeRange imports (fun startIDT endIDT =>
  makeRange exports (fun startEDT endEDT =>
  makePEfile dRVA targetType entry
  startEDT endEDT
  startIDT endIDT
  0 0
  ((if exports is _::_
   then [::EDATA (makeExportSection dRVA startEDT endEDT progName exports)]
   else nil) ++
   (if imports is _::_
   then [::IDATA (makeImportSection dRVA startIDT endIDT imports importAddrs)]
   else nil) ++ sections)))) t).


(* The "false" argument to runWriter ensures that we don't emit pad bytes for alignSkip
   directives. *)
Definition assembleToString (offset:DWORD) p :=
  if runWriter false write_program offset p is Some bytes then bytesToHex bytes else "ERROR"%string.

Definition makeEXE base progName t :=
  assembleToString base (makePEfile_program EXE progName t).
Definition makeDLL base progName t :=
  assembleToString base (makePEfile_program DLL progName t).
*)