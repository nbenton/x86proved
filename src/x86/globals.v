(*===========================================================================
  A first attempt at defining "modules" that export entry points
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat tuple seq eqtype fintype.
Require Import bitsrep bitsprops bitsops bitsopsprops instr instrrules procstate
        instrsyntax eval monad enc instrcodec tuplehelp.
Require Import SPred septac spec spectac safe basic program macros programassem programassemcorrect.
Require Import reader pointsto cursor.
Require Import Morphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
    Let's first show how to do it for module with a single export
  ---------------------------------------------------------------------------*)

(* A module that exports a single entry point is represented by a program
   parameterized on the entry point address *)
Record Module1 := {
  entry: DWORD -> program
  }.

(* We compile this module by preceding the code by the entry point *)
Definition compileModule1 (m:Module1) : program :=
  (LOCAL L;
  dd L;;    (* export table *)
  L:;; entry m L  (* code *)
  ).

(* Correctness statement is straightforward *)
Theorem assembleModule1_correct (offset endpos: DWORD) (m: Module1):
  assemble_success offset (compileModule1 m) = true ->
  offset -- endpos :-> assemble offset (compileModule1 m) |--
  Exists ploc:DWORD,
  offset :-> ploc ** offset +#4 -- endpos :-> (entry m ploc).
Proof.
move => H.
rewrite -> assemble_correct => //.
rewrite /compileModule1/dd. unfold_program.
sdestructs => ploc i1 i2 -> ->.
rewrite memIsDWORD_range. sdestruct => ->. rewrite /pointsTo.
sbazooka.
Qed.


(*---------------------------------------------------------------------------
    Now let's do it for a module with two exports
  ---------------------------------------------------------------------------*)

(* Each program is parameterized on the addresses of both programs *)
Record Module2 := {
  entry1: DWORD -> DWORD -> program;
  entry2: DWORD -> DWORD -> program}.

Definition compileModule2 (m:Module2) :=
  (LOCAL L1; LOCAL L2;
   dd L1;; dd L2;;  (* export table *)
   L1:;; entry1 m L1 L2;; (* code for entry1 *)
   L2:;; entry2 m L1 L2)  (* code for entry2 *)
  .

(* Correctness is not much harder than for a single export *)
Theorem assembleModule2_correct (offset endpos: DWORD) (m: Module2):
  assemble_success offset (compileModule2 m) = true ->
  offset -- endpos :-> assemble offset (compileModule2 m) |--
  Exists ploc1:DWORD, Exists ploc2:DWORD,
  offset :-> ploc1 **
  offset +#4 :-> ploc2 **
  ploc1 :-> entry1 m ploc1 ploc2 **
  ploc2 :-> entry2 m ploc1 ploc2.
Proof.
move => H.
rewrite -> assemble_correct => //.
rewrite /compileModule2/dd. unfold_program.
sdestructs => ploc1 ploc2 i1 i2 i3 -> -> i4 i5 -> ->.
rewrite (memIsDWORD_range _ _ ploc1). sdestruct => ->.
rewrite (memIsDWORD_range _ _ ploc2). sdestruct => ->.
rewrite /pointsTo. sbazooka.
Qed.


(*---------------------------------------------------------------------------
    Now the hard bit: n-ary modules

    We could use various existing libraries for n-ary objects such as n.-tuple (ssreflect)
    and nprod/nfun (from NaryFunctions in the standard distribution).
    However, for unknown reasons I ran into universe inconsistencies when
    using these, so here we define specialized versions, using n.-tuple only to
    collect n programs together.
  ---------------------------------------------------------------------------*)

Fixpoint nary (T: Type) n := if n is n.+1 then DWORD -> nary T n else T.

Fixpoint nDWORD n : Type := if n is n.+1 then (DWORD * nDWORD n)%type else unit.

Fixpoint makeNary T n : (nDWORD n -> T) -> nary T n :=
  if n is n.+1
  then fun f => fun d => makeNary (fun ds => f (d,ds))
  else fun p => p tt.

Fixpoint applyNary T n : nary T n -> (nDWORD n -> T) :=
  if n is n.+1
  then fun body ds => applyNary (body ds.1) ds.2
  else fun body ds => body.

Lemma applyMakeNary T n (f: nDWORD n -> T) ds :
  applyNary (makeNary f) ds = f ds.
Proof. induction n.
+ by elim ds.
+ elim ds => [d ds']. by rewrite /= IHn.
Qed.

Fixpoint fmapNary T n (f: T -> T) : nary T n -> nary T n :=
  if n is n.+1
  then fun spec lbl => fmapNary f (spec lbl)
  else fun spec => f spec.

Lemma applyFmapNary T (n: nat) (f: T -> T) (t: nary T n) (args: nDWORD n) :
  applyNary (fmapNary f t) args = f (applyNary t args).
Proof.
  induction n.
  + reflexivity.
  + destruct args.
    by rewrite /= IHn.
Qed.

Fixpoint liftNary T n (t: T) : nary T n :=
  if n is n.+1
  then fun _ => liftNary n t
  else t.

Fixpoint dropFirstArgs T n a : nary T a -> nary T (n + a) :=
  if n is n.+1
  then fun p _ => dropFirstArgs n p
  else fun p => p.

Fixpoint dropAllArgs T n (t: T) : nary T n :=
  if n is n.+1
  then fun _ => dropAllArgs n t
  else t.

Fixpoint dropLastArgs T n a : nary T a -> nary T (a + n) :=
  if a is a'.+1
  then fun t x => dropLastArgs n (t x)
  else fun t => dropAllArgs n t.

Fixpoint splitnDWORD a b : nDWORD (a + b) -> (nDWORD a * nDWORD b) :=
  if a is a.+1
  then fun p =>
    let: (a', b') := splitnDWORD (snd p) in
    ((fst p, a'), b')
  else fun b' => (tt, b').

Lemma applyNaryDropFirstArgs T m n (t: nary T n) (l: nDWORD (m + n)) l1 (l2: nDWORD n) :
  splitnDWORD l = (l1, l2) ->
  applyNary (dropFirstArgs m t) l = applyNary t l2.
Proof.
  induction m.
  + inversion 1; subst.
    reflexivity.
  + destruct l as [lbl l].
    destruct l1 as [lbl' l1].
    rewrite /=.
    case SPLIT : (splitnDWORD l) => EQ.
    inversion EQ; clear EQ; subst.
    by apply IHm with (l1 := l1).
Qed.

Lemma applyNaryDropLastArgs T m n (t: nary T m) (l: nDWORD (m + n)) l1 (l2: nDWORD n) :
  splitnDWORD l = (l1, l2) ->
  applyNary (dropLastArgs n t) l = applyNary t l1.
Proof.
  induction m.
  + inversion 1; subst.
    rewrite /=.
    induction n.
    - reflexivity.
    - destruct l2 as [l l2].
      by apply IHn.
  + destruct l as [lbl l].
    destruct l1 as [lbl' l1].
    rewrite /=.
    case SPLIT : (splitnDWORD l) => EQ.
    inversion EQ; clear EQ; subst.
    by apply IHm with (l1 := l1).
Qed.

Fixpoint prog_decnlabel n : nary program n -> program :=
  if n is n.+1
  then fun p => LOCAL L; prog_decnlabel (p L)
  else fun p => p.

Lemma programMemIsNLabel (p q: DWORD) n (body : nary program n) :
  p -- q :-> prog_decnlabel body -|- Exists ds, p -- q :-> applyNary body ds.
Proof.
induction n.
+ simpl. split. sbazooka. sdestruct => _. reflexivity.
+ rewrite /prog_decnlabel-/prog_decnlabel.
  unfold_program. split.
  - sdestruct => d. rewrite -> IHn. sdestruct => ds. apply lexistsR with (d,ds). by simpl.
  - sdestruct => ds. destruct ds as [d ds]. apply lexistsR with d. rewrite -> IHn.
    apply lexistsR with ds. reflexivity.
Qed.

Fixpoint naryDd n : nDWORD n -> program :=
  if n is n.+1
  then fun exports => dd exports.1;; naryDd exports.2
  else fun exports => prog_skip.

Fixpoint memIs_nDWORD (p q:DWORD) n : nDWORD n -> SPred :=
  if n is n.+1
  then fun ds => p -- (p+#4) :-> ds.1 ** memIs_nDWORD (p+#4) q ds.2
  else fun ds => p = q /\\ empSP.

Lemma programMemIsNaryDd n : forall (p q: DWORD) (ds: nDWORD n),
  p -- q :-> naryDd ds -|- memIs_nDWORD p q ds.
Proof. induction n.
+ simpl. reflexivity.
+ move => p q ds. destruct ds as [d ds]. rewrite /naryDd-/naryDd/fst/snd.
  rewrite /memIs_nDWORD-/memIs_nDWORD/fst/snd.
  unfold_program. rewrite <- IHn. rewrite /dd.
  split.
  - sdestruct => i. rewrite programMemIsData memIsDWORD_range. sdestruct => ->. reflexivity.
  - ssplit. rewrite programMemIsData. reflexivity.
Qed.

(* A module that exports n entry points is represented by an n-tuple of
   programs each parameterized on the addreses of all n entry points *)
Record naryModule n :=
{ moduleAssumptions : spec
; modulePrograms    : n.-tuple (nary program n)
; moduleSpecs       : n.-tuple (DWORD -> spec)
; moduleGuarantees  : spec
}.
Arguments Build_naryModule n moduleAssumptions modulePrograms moduleSpecs moduleGuarantees.

Fixpoint prog_nlabelaux alln (alllabels : nDWORD alln) n :=
  if n is n.+1 return nDWORD n -> n.-tuple (nary program alln) -> program
  then fun labels entries =>
    labels.1:;;
    applyNary (thead entries) alllabels;;
    prog_nlabelaux alllabels n labels.2 (behead_tuple entries)
  else fun labels entries => prog_skip.

Definition prog_nlabel n labels (entries: n.-tuple (nary program n)) :=
  prog_nlabelaux labels labels entries.

Open Scope instr_scope.

(* We compile an n-ary module by preceding the code by a table of entry points *)
Definition compileNaryModule n (m: naryModule n) :=
  prog_decnlabel (makeNary
    (fun labels =>
    naryDd labels;;                 (* export table *)
    prog_nlabel labels (modulePrograms m) (* code *)
  )).

(* The letrec-like definition of n labelled naryPrograms requires a little generalization
   in order to get induction to work *)
Fixpoint entriesSPred alln (alllabels: nDWORD alln) n : nDWORD n -> n.-tuple (nary program alln) -> SPred
  :=
  if n is n.+1
  then fun labels entries =>
    labels.1 :-> applyNary (thead entries) alllabels **
      entriesSPred alllabels labels.2 (behead_tuple entries)
  else fun labels entries => empSP.

Lemma entries_correct alln (alllabels: nDWORD alln) n : forall (ds : nDWORD n) (offset endpos: DWORD) ps,
   offset -- endpos :-> prog_nlabelaux alllabels ds ps |-- entriesSPred alllabels ds ps.
Proof. induction n.
+ move => ds offset endpos ps.
  simpl. by sdestruct => _.
+ move => ds offset endpos ps. destruct ds as [d ds].
  simpl.
  sdestructs => i1 -> -> i2. ssimpl.
  rewrite -> IHn. simpl. rewrite /pointsTo. ssimpl.
  apply lexistsR with i2. by simpl.
Qed.

(* Compare correctness of 1- and 2-entry modules *)
Theorem assembleNaryModule_correct n (offset endpos: DWORD) (m: naryModule n):
  assemble_success offset (compileNaryModule m) = true ->
  offset -- endpos :-> assemble offset (compileNaryModule m) |--
  Exists labels,
  Exists i,
  memIs_nDWORD offset i labels ** entriesSPred labels labels (modulePrograms m).
Proof.
move => H.
rewrite -> assemble_correct => //.
rewrite /compileNaryModule.
rewrite programMemIsNLabel. sdestruct => ds.
rewrite applyMakeNary.
unfold_program. sdestruct => i.
rewrite programMemIsNaryDd.
apply lexistsR with ds.
apply lexistsR with i. ssimpl.
apply entries_correct.
Qed.

Fixpoint landSpecs n : n.-tuple spec -> spec :=
  if n is n.+1
  then fun t => thead t //\\ landSpecs (behead_tuple t)
  else fun _ => ltrue.

Definition readFrameAtom n (p: nary program n) (labels: nDWORD n) (lbl: DWORD) :=
  Exists lblEnd : DWORD, lbl -- lblEnd :-> applyNary p labels.

Fixpoint readFrame' alln (alllabels: nDWORD alln) n : n.-tuple (nary program alln) -> nDWORD n -> SPred :=
  if n is n.+1
  then fun ps lbls =>
    let: (lbl, lbls) := lbls in
    readFrameAtom (thead ps) alllabels lbl ** readFrame' alllabels (behead_tuple ps) lbls
  else fun _ _ => empSP.

Definition readFrame n (ps: n.-tuple (nary program n)) (lbls: nDWORD n) : SPred :=
  readFrame' lbls ps lbls.

Fixpoint applyEachSpec n : nDWORD n -> n.-tuple (DWORD -> spec) -> n.-tuple spec :=
  if n is n.+1
  then
    fun lbls specs =>
      let: (lbl, lbls) := lbls in
      [tuple of thead specs lbl :: applyEachSpec lbls (behead_tuple specs) ]
  else
    fun _ _ => [tuple].

Definition mapReadFrame (f: SPred) (n: nat) (t: n.-tuple spec) : n.-tuple spec :=
  map_tuple (fun s => s <@ f) t.

Definition inSomeContext (s: spec) : spec :=
  Exists context, s <@ context.

Definition framedSpecs (n: nat) (m: naryModule n) (labels: nDWORD n) :=
  map_tuple inSomeContext (applyEachSpec labels (moduleSpecs m)).

Definition moduleSpec n (m: naryModule n) (labels: nDWORD n) : spec :=
  landSpecs (framedSpecs m labels).

Definition relativeCorrectness' (assumptions: spec) alln n (allspecs: alln.-tuple spec) (specs: n.-tuple spec) :=
  forall (i: 'I_n),
    |> (assumptions -->> landSpecs allspecs)
    |--
    assumptions -->> tnth specs i.

Definition relativeCorrectness (n: nat) (m: naryModule n) :=
  forall (labels: nDWORD n),
    relativeCorrectness' (moduleAssumptions m) (framedSpecs m labels) (framedSpecs m labels).

Lemma relativeCorrectnessSufficient
      (assumptions: spec) alln n (allspecs: alln.-tuple spec) (specs: n.-tuple spec) :
  relativeCorrectness' assumptions allspecs specs ->
  |> (assumptions -->> landSpecs allspecs)
  |--
  assumptions -->> landSpecs specs.
Proof.
  move => H. induction n.
  + apply limplAdj. by apply ltrueR.
  + move : H.
    case : specs / tupleP => spec specs.
    rewrite / relativeCorrectness' / landSpecs -/ landSpecs.
    autorewrite with tuple.
    move => H.
    apply limplAdj; apply landR; apply landAdj.
    - apply (H ord0).
    - rewrite <- (IHn specs).
      + reflexivity.
      + move => i.
        rewrite -> (H (inord (i.+1))).
        rewrite / tnth inordK /=; last by destruct i.
        erewrite -> set_nth_default; first reflexivity.
        move : specs H => [tval TVAL] H /=.
        by rewrite (eqP TVAL).
Qed.

Definition completeness (n: nat) (m: naryModule n) :=
  forall (labels: nDWORD n),
    moduleAssumptions m //\\ moduleSpec m labels
    |--
    inSomeContext (moduleGuarantees m).

Definition moduleCorrect n (m: naryModule n) : Prop :=
  forall (labels: nDWORD n),
    moduleAssumptions m
    |--
    moduleSpec m labels //\\ inSomeContext (moduleGuarantees m).

Theorem relativeCorrectnessImplies n (m: naryModule n) :
  relativeCorrectness m ->
  forall (labels: nDWORD n),
    moduleAssumptions m |-- moduleSpec m labels.
Proof.
  move => COR labels.
  apply limplValid.
  apply spec_lob.
  rewrite / moduleSpec.
  apply relativeCorrectnessSufficient.
  by apply COR.
Qed.

Theorem relativeCorrectnessCompletenessSufficient n (m: naryModule n) :
  relativeCorrectness m ->
  completeness m ->
  moduleCorrect m.
Proof.
  move => COR COM labels.
  apply landR.
  + by apply relativeCorrectnessImplies.
  + rewrite /completeness in COM. rewrite <-(COM labels).
    apply landR; first by reflexivity.
    by apply relativeCorrectnessImplies.
Qed.

Definition mergePrograms
           alln1 alln2 n1 n2
           (p1: n1.-tuple (nary program alln1))
           (p2: n2.-tuple (nary program alln2)) :=
  cat_tuple
    (map_tuple (dropLastArgs  (a := alln1) alln2) p1)
    (map_tuple (dropFirstArgs (a := alln2) alln1) p2).

Definition link2 (n1 n2: nat) (m1: naryModule n1) (m2: naryModule n2)
           (newAssumptions: spec) (newGuarantees: spec) :
  naryModule (n1 + n2) :=
  let: Build_naryModule _ prog1 spec1 _ := m1 in
  let: Build_naryModule _ prog2 spec2 _ := m2 in
  Build_naryModule
    newAssumptions
    (mergePrograms prog1 prog2)
    (cat_tuple spec1 spec2)
    newGuarantees.

(*
Lemma link2_lemma s1 s2 f1 f2 f3 :
  f3 |-- f1 ->
  f3 |-- f2 ->
  s1 <@ f1 //\\ s2 <@ f2 |-- (s1 //\\ s2) <@ f3.
Proof.
  move => F1 F2.
  specsplit.
  + apply landL1. by apply spec_reads_entails.
  + apply landL2. by apply spec_reads_entails.
Qed.

(* this one is NOT provable using link2_lemma because f1 ** f2 |-/- f1*)
Lemma link2_lemma2 s1 s2 f1 f2 :
  s1 <@ f1 //\\ s2 <@ f2 |-- (s1 //\\ s2) <@ (f1 ** f2).
Proof.
  rewrite <- spec_reads_merge.
  specsplit.
  + apply landL1. by apply spec_reads_frame.
  + apply landL2. rewrite spec_reads_swap. by apply spec_reads_frame.
Qed.

Lemma link2_lemma3 s1 s2 f1 f2 :
  s1 <@ f1 //\\ s2 <@ f2 |-- (s1 //\\ s2) <@ (f1 ** f2 ** ltrue).
Proof.
  specsplit.
  + apply landL1. rewrite <- spec_reads_merge. by apply spec_reads_frame.
  + apply landL2. rewrite sepSPC. rewrite -> sepSPA. rewrite <- spec_reads_merge. by apply spec_reads_frame.
Qed.
*)

Lemma decomposeReadFrame
      alln1 alln2 n1 n2
      (p1: n1.-tuple (nary program alln1)) p2
      (alllabels: nDWORD (alln1 + alln2)) (alllabels1: nDWORD alln1) (alllabels2: nDWORD alln2)
      (labels: nDWORD (n1 + n2)) (labels1: nDWORD n1) (labels2: nDWORD n2) :
  splitnDWORD alllabels = (alllabels1, alllabels2) ->
  splitnDWORD labels = (labels1, labels2) ->
  readFrame' alllabels (mergePrograms p1 p2) labels
  |--
  readFrame' alllabels1 p1 labels1 ** readFrame' alllabels2 p2 labels2.
Proof.
  move => ALBLS.
  induction n1.
  + rewrite (tuple0 p1) / mergePrograms mapNil catNil /=.
    move => LBLS; inversion LBLS; clear LBLS; subst.
    sbazooka.
    clear p1.
    induction alln1.
    - rewrite mapId.
      inversion ALBLS; clear ALBLS; subst.
      reflexivity.
    - destruct alllabels as [label alllabels].
      destruct alllabels1 as [label1 alllabels1].
      move : ALBLS; rewrite /=.
      case SPLIT : (splitnDWORD alllabels) => EQ; inversion EQ; clear EQ; subst.
      rewrite <- IHalln1; eauto; clear IHalln1.
      induction n2.
      + reflexivity.
      + destruct labels2 as [label2 labels2].
        case : p2 / tupleP => p p2.
        rewrite /=.
        apply sepSP_lentails_m.
        - reflexivity.
        - autorewrite with tuple.
          apply IHn2.
  + destruct labels as [label labels].
    destruct labels1 as [label1 labels1].
    case : p1 / tupleP => p p1 /=.
    case SPLIT : (splitnDWORD labels) => EQ; inversion EQ; clear EQ; subst.
    rewrite / mergePrograms.
    autorewrite with tuple.
    rewrite sepSPA.
    apply sepSP_lentails_m.
    - rewrite / readFrameAtom /=.
      erewrite applyNaryDropLastArgs; last by eauto.
      reflexivity.
    - by apply IHn1.
Qed.

Global Instance inSomeContext_lentails_m : Proper (lentails ==> lentails) inSomeContext.
Proof.
  move => s1 s2 H.
  apply lexistsL; move => f.
  apply lexistsR with f.
  apply spec_reads_entails; [ assumption | reflexivity ].
Qed.

Lemma landSpecsCat
      n1 n2
      (s1: n1.-tuple (DWORD -> spec)) (s2: n2.-tuple (DWORD -> spec))
      (labels: nDWORD (n1 + n2)) (labels1: nDWORD n1) (labels2: nDWORD n2) :
  splitnDWORD labels = (labels1, labels2) ->
  landSpecs (map_tuple inSomeContext (applyEachSpec labels1 s1))
  //\\
  landSpecs (map_tuple inSomeContext (applyEachSpec labels2 s2))
  |--
  landSpecs (map_tuple inSomeContext (applyEachSpec labels (cat_tuple s1 s2))).
Proof.
  move => LABELS.
  induction n1.
  + rewrite (tuple0 s1); clear s1.
    apply landL2.
    autorewrite with tuple.
    inversion LABELS; clear LABELS; subst.
    reflexivity.
  + case : s1 / tupleP => [spec specs1] /=.
    destruct labels as [label labels].
    destruct labels1 as [label1 labels1].
    move : LABELS.
    rewrite /=.
    case SPLIT : (splitnDWORD labels) => EQ; inversion EQ; clear EQ; subst.
    repeat rewrite mapCons.
    autorewrite with tuple.
    rewrite landA.
    apply land_lentails_m.
    - reflexivity.
    - by apply IHn1.
Qed.

Theorem link2_correct (n1 n2: nat) (m1: naryModule n1) (m2: naryModule n2)
        (newAssumptions: spec) (newGuarantees: spec) :
  moduleCorrect m1 ->
  moduleCorrect m2 ->
  newAssumptions |-- moduleAssumptions m1 //\\ moduleAssumptions m2 ->
  inSomeContext (moduleGuarantees m1) //\\ inSomeContext (moduleGuarantees m2) |-- inSomeContext newGuarantees ->
  moduleCorrect (link2 m1 m2 newAssumptions newGuarantees).
Proof.
  move : m1 m2 => [assu1 prog1 spec1 guar1] [assu2 prog2 spec2 guar2].
  rewrite / moduleCorrect / moduleSpec / framedSpecs /=.
  move => COR1 COR2 ASSU GUAR labels.
  move LABELS : (splitnDWORD labels) => [labels1 labels2].
  specialize (COR1 labels1).
  specialize (COR2 labels2).
  rewrite -> ASSU.
  apply landR.
  + rewrite -> land_lentails_m; [ | apply COR1 | apply COR2].
    rewrite <- landA.
    rewrite -> landL1; last reflexivity.
    rewrite landC.
    rewrite <- landA.
    rewrite -> landL1; last reflexivity.
    rewrite landC / mapReadFrame / readFrame.
    by apply landSpecsCat.
  + rewrite <- GUAR.
    apply land_lentails_m.
    - rewrite -> COR1.
      by apply landL2.
    - rewrite -> COR2.
      by apply landL2.
Qed.

(* Example: mutually recursive odd/even, with argument in ECX, result (0 or 1) in EAX *)
(* Obviously this is a very silly way of determining parity in assembler! *)
Example evenEntry : nary program 2 :=
  (fun even odd =>
    (CMP ECX, 0;;
     ifthenelse CC_Z true
       (MOV EAX, 1;; RET 0)
       (DEC ECX;; JMP odd))).

Example oddEntry : nary program 2 :=
  (fun even odd =>
    (CMP ECX, 0;;
     ifthenelse CC_Z true
       (MOV EAX, 0;; RET 0)
       (DEC ECX;; JMP even))).

(* We will prove that running odd (resp. even) is essentially equivalent to storing the least
   significant bit of ECX (resp. its complement) in EAX. *)
Definition evenSpec (dEven: DWORD) :=
Forall n: DWORD, Forall sp : DWORD, Forall ret: DWORD,
(
safe @ (EIP ~= ret   ** EAX ~= #(~~ lsb n) ** ECX?     ** ESP?         ** sp-#4 :-> ?:DWORD)
-->>
safe @ (EIP ~= dEven ** EAX?               ** ECX ~= n ** ESP ~= sp-#4 ** sp-#4 :-> ret    )
)
@ (EDX? ** OSZCP?).

Definition oddSpec (dOdd: DWORD) :=
Forall n: DWORD, Forall sp : DWORD, Forall ret: DWORD,
(
safe @ (EIP ~= ret  ** EAX ~= #(lsb n) ** ECX?     ** ESP?         ** sp-#4 :-> ?:DWORD)
-->>
safe @ (EIP ~= dOdd ** EAX?            ** ECX ~= n ** ESP ~= sp-#4 ** sp-#4 :-> ret    )
)
@ (EDX? ** OSZCP?).

(* We build a module exposing the existence of even and odd *)
Example parityModule : naryModule 2 :=
  Build_naryModule
    (n:=2)
    ltrue
    [tuple evenEntry; oddEntry]
    [tuple evenSpec;  oddSpec]
    (Exists dEven : DWORD, Exists dOdd  : DWORD, evenSpec dEven //\\ oddSpec dOdd).

Lemma lsbdecB : forall n (b: BITS n.+1),
  lsb (decB b) = ~~ lsb b.
Proof.
  rewrite / negb / lsb.
  induction n.
  + move => [ [ | [|] l ] S].
    - by inversion S.
    - by compute.
    - by compute.
  + destruct b as [l S].
    specialize (IHn (behead_tuple (Tuple S))).
    move : IHn.
    destruct l as [|[|] l]; inversion_clear S; by rewrite S /=.
Qed.

Fixpoint nthDWORD n : nDWORD n -> 'I_n -> DWORD.
Proof.
  induction n.
  + by move => _ [? ?].
  + move => [dword dwords] [[|i] LT].
    - exact dword.
    - refine (nthDWORD _ dwords (Ordinal _)).
      apply LT.
Defined.

(* This helper makes it easy to state each function's correctness in a module.
   Just write theorems of type [relativelyCorrect yourModule i] for each natural
   number i less than your number of programs. *)
Definition relativelyCorrect n (m: naryModule n) (i: nat) :=
  forall (P: i < n) (labels : nDWORD n),
    |> (moduleAssumptions m -->> moduleSpec m labels)
    |--
    moduleAssumptions m -->>
    tnth (framedSpecs m labels) (Ordinal P).

Theorem later_inSomeContext S :
  |> inSomeContext S
  |-- inSomeContext (|> S).
Proof.
  rewrite / inSomeContext.
  transitivity (Exists context, |> (S <@ context)); last first.
  apply lexistsL; move => f; apply lexistsR with f.
  by rewrite -> spec_reads_later.
  rewrite -> spec_later_exists_inhabited; first reflexivity.
  constructor.
  by apply mkSPred with (P := fun _ => ltrue).
Qed.

Theorem inSomeContext_grab f s :
  inSomeContext (s <@ f) |-- inSomeContext s.
Proof.
  apply lexistsL; move => f'.
  rewrite -> spec_reads_merge.
  by apply lexistsR with (f ** f').
Qed.

Theorem evenRelativelyCorrect : relativelyCorrect parityModule 0.
Proof.
  move => P [evenStart [oddStart []]] /=.
  rewrite SpecApply.limpltrue SpecApply.limpltrue.
  rewrite / moduleSpec /= / thead / tnth /=.
  (* get rid of useless premisses *)
  rewrite -> landL2; last by reflexivity.
  rewrite -> landL1; last by reflexivity.
  rewrite -> later_inSomeContext.
  etransitivity; last by apply
  (inSomeContext_grab (f := readFrameAtom evenEntry (evenStart, (oddStart, tt)) evenStart)).
  apply inSomeContext_lentails_m.
  (* unfold *)
  autorewrite with tuple.
  rewrite theadCons.
  rewrite / readFrameAtom / applyNary / evenSpec / programMemIs / evenEntry.
  simpl fst. simpl snd.
  specintros => evenEnd n sp ret.
  unfold_program.
  specintros => c1.
  (* perform CMP ECX, 0 *)
  specapply CMP_RI_ZC_rule; first by sbazooka.
  (* unfold more *)
  rewrite / ifthenelse.
  unfold_program.
  specintros => dThen dElse c2 c3 c4 c5 c6 EQ0 EQ1 c7 c8 EQ2 EQ3. subst c5 c6 c7 dElse.
  (* perform JZ dThen *)
  specapply JZ_rule; first by sbazooka.
  autorewrite with push_at.
  specsplit.
  (* then branch *)
  + (* get |> out of the way *)
    rewrite -> (spec_later_weaken (safe @ _)).
    rewrite <- spec_later_impl.
    rewrite -> spec_reads_later.
    apply spec_later_entails.
    specintros => N0.
    (* in this branch we don't need odd's spec *)
    etransitivity; first by apply ltrueR.
    (* perform MOV EAX, 1 *)
    specapply (MOV_RanyI_rule (r := EAX)); first by sbazooka.
    (* perform RET *)
    specapply RET_rule; first by sbazooka.
    (* drop the read frame and massage the goal, quite clumsy *)
    rewrite <- spec_reads_frame.
    autorewrite with push_at.
    apply limplAdj; apply landL2.
    rewrite -> spec_later_weaken.
    apply limplValid.
    rewrite <- spec_later_impl.
    rewrite <- spec_later_weaken.
    apply limplAdj; apply landL2.
    apply at_contra.
    sbazooka.
    move : N0; case : (@eqP _ n #0) => N0 EQ; last easy; move : EQ => _.
    subst n.
    rewrite /stateIsAny. sbazooka. reflexivity.
  (* else branch *)
  + specintros => N0.
    specapply DEC_R_ruleNoFlags.
    sbazooka.
    rewrite {3 4}/stateIsAny. sbazooka.

    specapply JMP_I_rule; first by sbazooka.
    autorewrite with push_at.
    rewrite -> (spec_later_weaken (safe @ _)).
    rewrite <- spec_later_impl.
    rewrite -> spec_reads_later.
    apply spec_later_entails.
    rewrite -> spec_reads_frame.
    apply spec_reads_entails; last reflexivity.
    rewrite / oddSpec.
    apply lforallL with (x := (decB n)).
    apply lforallL with (x := sp).
    apply lforallL with (x := ret).
    autorewrite with push_at.
    apply limpl_lentails_m.
    - by rewrite / Basics.flip lsbdecB.
    - apply at_contra.
      by sbazooka.
Qed.

Theorem oddRelativelyCorrect : relativelyCorrect parityModule 1.
Proof.
  move => P [evenStart [oddStart []]] /=.
  rewrite SpecApply.limpltrue SpecApply.limpltrue.
  rewrite / moduleSpec /= / thead / tnth /=.
  (* get rid of useless premisses *)
  rewrite -> spec_later_and.
  rewrite -> landL1; last by reflexivity.
  rewrite -> later_inSomeContext.
  etransitivity; last by apply
  (inSomeContext_grab (f := readFrameAtom oddEntry (evenStart, (oddStart, tt)) oddStart)).
  apply inSomeContext_lentails_m.
  (* unfold *)
  autorewrite with tuple.
  rewrite theadCons.
  rewrite / readFrameAtom / applyNary / oddSpec / programMemIs / oddEntry.
  simpl fst. simpl snd.
  specintros => oddEnd n sp ret.
  unfold_program.
  specintros => c1.
  (* perform CMP ECX, 0 *)
  specapply CMP_RI_ZC_rule; first by sbazooka.
  (* unfold more *)
  rewrite / ifthenelse.
  unfold_program.
  specintros => dThen dElse c2 c3 c4 c5 c6 EQ0 EQ1 c7 c8 EQ2 EQ3. subst c5 c6 c7 dElse.
  (* perform JZ dThen *)
  specapply JZ_rule; first by sbazooka.
  autorewrite with push_at.
  specsplit.
  (* then branch *)
  + (* get |> out of the way *)
    rewrite -> (spec_later_weaken (safe @ _)).
    rewrite <- spec_later_impl.
    rewrite -> spec_reads_later.
    apply spec_later_entails.
    specintros => N0.
    (* in this branch we don't need even's spec *)
    etransitivity; first by apply ltrueR.
    (* perform MOV EAX, 0 *)
    specapply (MOV_RanyI_rule (r := EAX)); first by sbazooka.
    (* perform RET *)
    specapply RET_rule; first by sbazooka.
    (* drop the read frame and massage the goal, quite clumsy *)
    rewrite <- spec_reads_frame.
    autorewrite with push_at.
    apply limplAdj. apply landL2.
    rewrite -> spec_later_weaken.
    apply limplValid.
    rewrite <- spec_later_impl.
    rewrite <- spec_later_weaken.
    apply limplAdj. apply landL2.
    apply at_contra.
    sbazooka.
    move : N0; case : (@eqP _ n #0) => N0 EQ; last easy; move : EQ => _.
    subst n. rewrite /stateIsAny. sbazooka.
    reflexivity.
  (* else branch *)
  + specintros => N0.
    specapply DEC_R_ruleNoFlags.
    rewrite  {8 9}/stateIsAny. sbazooka.
    specapply JMP_I_rule; first by sbazooka.
    autorewrite with push_at.
    rewrite -> (spec_later_weaken (safe @ _)).
    rewrite <- spec_later_impl.
    rewrite -> spec_reads_later.
    apply spec_later_entails.
    rewrite -> spec_reads_frame.
    apply spec_reads_entails; last reflexivity.
    rewrite / evenSpec.
    apply lforallL with (x := decB n).
    apply lforallL with (x := sp).
    apply lforallL with (x := ret).
    autorewrite with push_at.
    apply limpl_lentails_m.
    - by rewrite / Basics.flip lsbdecB Bool.negb_involutive.
    - apply at_contra. by sbazooka.
Qed.

Theorem mergeContexts s1 s2 s :
  s1 //\\ s2 |-- s ->
  (Exists c1, s1 <@ c1) //\\ (Exists c2, s2 <@ c2)
  |--
  Exists c, s <@ c.
Proof.
  move => H.
  (* shouldn't specintros grab these existentials? *)
  apply landAdj; apply lexistsL; move => c1; apply limplAdj.
  rewrite landC.
  apply landAdj; apply lexistsL; move => c2; apply limplAdj.
  rewrite landC.
  apply lexistsR with (c1 ** c2).
  transitivity ((s1 //\\ s2) <@ (c1 ** c2)).
  + rewrite -> spec_reads_and.
    apply land_lentails_m.
    - rewrite <- spec_reads_merge.
      by rewrite <- (spec_reads_frame (R := c2)).
    - rewrite <- spec_reads_merge.
      by rewrite <- (spec_reads_frame (R := c1)).
  + apply spec_reads_entails; [ assumption | reflexivity ].
Qed.

Theorem parityModuleCorrect : moduleCorrect parityModule.
Proof.
  apply relativeCorrectnessCompletenessSufficient.
  + move => [lEven [lOdd []]].
    move => [ [|[|i]] LT]; last discriminate.
    apply evenRelativelyCorrect.
    apply oddRelativelyCorrect.
  + move => [lEven [lOdd []]].
    apply landL2.
    rewrite / moduleSpec / framedSpecs / mapReadFrame /=.
    autorewrite with tuple.
    rewrite <- landA.
    apply landL1.
    rewrite / inSomeContext.
    apply mergeContexts.
    apply lexistsR with lEven.
    apply lexistsR with lOdd.
    reflexivity.
Qed.

Example mainEntry (lEven lOdd: DWORD) : nary program 1 :=
  (fun main =>
    MOV ECX, 42;;
    JMP lEven).

Definition mainSpec (lEven lOdd lMain: DWORD) :=
Forall sp : DWORD, Forall ret: DWORD,
(
safe @ (EIP ~= ret   ** EAX ~= #1 ** ESP?         ** sp-#4 :-> ?:DWORD)
-->>
safe @ (EIP ~= lMain ** EAX?      ** ESP ~= sp-#4 ** sp-#4 :-> ret    )
)
@ (ECX? ** EDX? ** OSZCP?).

Example mainModule lEven lOdd : naryModule 1 :=
  Build_naryModule
    (n:=1)
    (evenSpec lEven //\\ oddSpec  lOdd)
    [tuple (mainEntry lEven lOdd)]
    [tuple (mainSpec lEven lOdd)]
    (Exists lMain: DWORD, mainSpec lEven lOdd lMain).

Theorem later_modus A B C D :
  C |-- A ->
  B |-- D ->
  |> (A -->> B) //\\ C |-- |> D.
Proof.
  move => CA BD.
  rewrite -> land_lentails_m; [ | reflexivity | by apply CA ].
  rewrite -> land_lentails_m; [ | reflexivity | by apply spec_later_weaken ].
  rewrite <- spec_later_and.
  apply spec_later_entails.
  apply landAdj.
  apply limpl_lentails_m; [ reflexivity | assumption ].
Qed.

Theorem modus A B C D :
  C |-- A ->
  B |-- D ->
  (A -->> B) //\\ C |-- D.
Proof.
  move => CA BD.
  rewrite -> land_lentails_m; [ | reflexivity | by apply CA ].
  apply landAdj.
  apply limpl_lentails_m; [ reflexivity | assumption ].
Qed.

Theorem mainRelativelyCorrect (lEven lOdd: DWORD) : relativelyCorrect (mainModule lEven lOdd) 0.
Proof.
  move => P [lMain []] /=.
  etransitivity; first by apply ltrueR.
  apply limplAdj; apply landL2.
  apply landL1.
  rewrite / tnth /=.
  apply lexistsR with (readFrameAtom (mainEntry lEven lOdd) (lMain, tt) lMain).
  autorewrite with tuple.
  rewrite / mainSpec / readFrameAtom / mainEntry / applyNary.
  specintros => mainEnd sp ret.
  autorewrite with push_at.
  unfold_program.
  specintros => c1.
  (* perform MOV ECX, #42 *)
  specapply (MOV_RanyI_rule (r := ECX)); first by sbazooka.
  specapply JMP_I_rule; first by sbazooka.
  rewrite -> spec_reads_frame.
  apply spec_reads_entails; last by reflexivity.
  apply lforallL with #42.
  apply lforallL with sp.
  apply lforallL with ret.
  autorewrite with push_at.
  apply limplAdj.
  rewrite <- spec_later_weaken.
admit.   (*apply modus.
  - apply AtContra_safe.
    sbazooka.
    reflexivity.
  - apply AtContra_safe.
    sbazooka.*)
Qed.


Theorem mainModuleCorrect lEven lOdd : moduleCorrect (mainModule lEven lOdd).
Proof.
  apply relativeCorrectnessCompletenessSufficient.
  + move => [lMain []].
    move => [ [|i] LT]; last discriminate.
    apply mainRelativelyCorrect.
  + move => [lMain []].
    apply landL2.
    rewrite / moduleSpec / framedSpecs / mapReadFrame /=.
    autorewrite with tuple.
    apply landL1.
    apply inSomeContext_lentails_m.
    apply lexistsR with lMain.
    reflexivity.
Qed.

Compute assembleToString #0 (compileNaryModule parityModule).
