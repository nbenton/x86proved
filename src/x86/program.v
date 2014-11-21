Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.spred x86proved.cursor x86proved.reader x86proved.writer x86proved.roundtrip x86proved.x86.addr.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*=program *)
Inductive program :=
  prog_instr (c: Instr)
| prog_skip | prog_seq (p1 p2: program)
| prog_declabel (body: ADDR -> program)
| prog_label (l: ADDR)
| prog_data {T} {R: Reader T} {W: Writer T} (RT: Roundtrip R W) (v: T).
Coercion prog_instr: Instr >-> program.
(*=End *)

Require Import Ssreflect.tuple.

(* Instructions in instrsyntax are up to level 60, so delimiters need to be
   above that. *)
(*=programsyntax *)
Infix ";;" := prog_seq (at level 62, right associativity).
Notation "'LOCAL' l ';' p" := (prog_declabel (fun l => p))
  (at level 65, l ident, right associativity).
Notation "l ':;'" := (prog_label l)
  (at level 8, no associativity, format "l ':;'").
(*=End *)
Notation "l ':;;' p" := (prog_seq (prog_label l) p)
  (at level 8, p at level 65, right associativity,
   format "l ':;;'  p").

(*=dd *)
Definition db := prog_data RoundtripBYTE.
Definition dw := prog_data RoundtripWORD.
Definition dd := prog_data RoundtripDWORD.
Definition dq := prog_data RoundtripQWORD.
(*=End *)
Definition ds s := prog_data (@RoundtripTupleBYTE (String.length s)) (stringToTupleBYTE s).
Definition dsz s := ds s;; db #0.
Definition align m := prog_data (RoundtripAlign m) tt.
Definition alignWith b m := prog_data (RoundtripAlignWith b m) tt.
Definition pad m := prog_data (RoundtripPad m) tt.
Definition padWith b m := prog_data (RoundtripPadWith b m) tt.
Definition skipAlign m := prog_data (RoundtripSkipAlign m) tt.

(* Sometimes handy just to get nice output *)
Fixpoint linearizeWith (p: program) tail :=
  match p with
  | prog_skip => tail
  | prog_seq p1 p2 => linearizeWith p1 (linearizeWith p2 tail)
  | prog_declabel f => prog_declabel (fun d => linearizeWith (f d) tail)
  | _ => if tail is prog_skip then p else prog_seq p tail
  end.
Definition linearize p := linearizeWith p prog_skip.

Declare Reduction showprog :=
  cbv beta delta -[fromNat fromHex makeMOV makeBOP db dw dd dq ds align pad] zeta iota.

Fixpoint interpProgram (i j:ADDRCursor) prog :=
  match prog with
  | prog_instr c => i -- j :-> c
  | prog_skip => 
      match i with
      | mkCursor i0 =>
          match j with
          | mkCursor j0 => i0 = j0 /\\ empSP
          | top => i = j /\\ empSP
          end
      | top => i = j /\\ empSP
      end
  | prog_seq p1 p2 => Exists i', interpProgram i (mkCursor i') p1 ** interpProgram (mkCursor i') j p2
  | prog_declabel body => Exists l:ADDR, interpProgram i j (body l)
  | prog_label l => 
      match i with
      | mkCursor i0 =>
          match j with
          | mkCursor j0 => i0 = j0 /\\ i0 = l /\\ empSP
          | top => i = j /\\ i = mkCursor l /\\ empSP
          end
      | top => i = j /\\ i = mkCursor l /\\ empSP
      end
  | prog_data _ _ _ _ v => i -- j :-> v
  end.

Lemma interpProgramLeAux prog : forall p q, interpProgram p q prog |-- leCursor p q /\\ interpProgram p q prog.
Proof.
induction prog => p q; rewrite /interpProgram-/interpProgram.
+ apply memIsLe.
+ destruct p. destruct q; sdestruct => ->; rewrite leCursor_refl; sbazooka.
  sdestruct => ->; rewrite leCursor_refl; sbazooka.
+ sdestruct => p'. rewrite -> IHprog1.   rewrite -> IHprog2.
  sdestruct => H1. sdestruct => H2. rewrite (leCursor_trans H1 H2). sbazooka.
+ sdestruct => p'. rewrite -> H. sbazooka.
+ destruct p. destruct q; sdestructs => -> ->; rewrite leCursor_refl; sbazooka.
  sdestruct => ->; rewrite leCursor_refl; sbazooka.
+ apply memIsLe.
Qed.

Definition interpProgramLe p q prog := @interpProgramLeAux prog p q.

Global Instance programMemIs : MemIs program := Build_MemIs interpProgramLe.

Lemma programMemIsSkip (p q:ADDRCursor) : p -- q :-> prog_skip -|- p = q /\\ empSP.
Proof. destruct p => //. destruct q => //=. split. sdestruct => ->. sbazooka.
sdestruct => H. injection H => ->. sbazooka. destruct q => //=. Qed.

Lemma programMemIsInstr p q i : p -- q :-> prog_instr i -|- p -- q :-> i.
Proof. by reflexivity. Qed.

Lemma programMemIsData T R W (RT:Roundtrip R W) p q (d:T) : p -- q :-> prog_data _ d -|- p -- q :-> d.
Proof. by simpl. Qed.

Lemma programMemIsSeq p q p1 p2 :
  p -- q :-> prog_seq p1 p2 -|- Exists p', p -- mkCursor p' :-> p1 ** mkCursor p' -- q :-> p2.
Proof. by simpl. Qed.

Lemma programMemIsLabel (p q: ADDRCursor) l :
  p -- q :-> prog_label l -|- p = q /\\ p = mkCursor l /\\ empSP.
Proof. split.
destruct p => //. simpl. destruct q => //. sbazooka. by subst. by congruence.  
by simpl. sdestructs => -> ->. simpl. sbazooka.
Qed.

Lemma programMemIsLocal p q p1 :
  p -- q :-> prog_declabel p1 -|- Exists L, p -- q :-> (p1 L).
Proof. split => //=. Qed.

(*Require Import bitsops.
Lemma programMemIsAlign (p:DWORD) q m :
  p -- q :-> align m -|- apart (toNat (negB (lowWithZeroExtend m p))) p q /\\ p -- q :-> align m.
Proof. simpl.
rewrite /readPad. rewrite programMemIsData.
Qed.
*)

Module ProgramTactic.

  (* This is identical to prod/pair/fst/snd from the standard library, repeated
     here to ensure we have full control over the fs and sn names. Then we can
     safely unfold them with cbv without affecting unrelated user declarations.
   *)
  Record pr A B := pa { fs: A; sn: B }.

  (* This helper tactic takes a memIs assertion and returns an unfolded one. *)
  (* This uses the trick from CPDT in the chapter "Building a Reification Tactic
     that Recurses Under Binders" *)
  Ltac aux P :=
    let P := eval cbv [fs sn] in P in
    match P with
    | fun (x: ?X) => @?i x -- @?j x :-> (@?p1 x ;; @?p2 x) =>
        let P1 := aux (fun i'x: pr ADDRCursor X => i (sn i'x) -- fs i'x :-> p1 (sn i'x)) in
        let P2 := aux (fun i'x: pr ADDRCursor X => fs i'x -- j (sn i'x) :-> p2 (sn i'x)) in
        constr:(fun (x:X) => Exists i':ADDR, P1 (pa (mkCursor i') x) ** P2 (pa (mkCursor i') x))

    | fun (x: ?X) => @?i x -- @?j x :-> (@?l x :;) =>
        constr: (fun (x:X) =>
        match (i x) with
        | mkCursor i0 =>
          match (j x) with
          | mkCursor j0 => i0 = j0 /\\ i0 = (l x) /\\ empSP
          | top => (i x) = (j x) /\\ (i x) = mkCursor (l x) /\\ empSP
          end
        | top => (i x) = (j x) /\\ (i x) = mkCursor (l x) /\\ empSP
        end)

    | fun (x: ?X) => @?i x -- @?j x :-> (prog_instr (@?c x)) =>
        constr:(fun (x:X) => i x -- j x :-> c x)

    | fun (x: ?X) => @?i x -- @?j x :-> (@prog_data _ _ _ _ (@?c x)) =>
        constr:(fun (x:X) => i x -- j x :-> c x)

    | fun (x: ?X) => (@?i x) -- @?j x :-> (prog_skip) => 
      constr: (fun (x:X) => match (i x) with
      | mkCursor i0 =>
          match (j x) with
          | mkCursor j0 => i0 = j0 /\\ empSP
          | top => (i x) = (j x) /\\ empSP
          end
      | top => (i x) = (j x) /\\ empSP
      end)

    | fun (x: ?X) => @?i x -- @?j x :-> (prog_declabel (@?body x)) =>
        let P' := aux (fun lx: pr ADDR X =>
                      i (sn lx) -- j (sn lx) :-> body (sn lx) (fs lx)) in
        constr:(fun (x:X) => Exists l:ADDR, P' (pa l x))

    | _ => P
    end.

  Ltac unfold_program :=
    match goal with
    | |- context C [ @memIs program _ ?i ?j ?p ] =>
        let e := aux (fun (_: unit) => @memIs program _ i j p) in
        let e := eval cbv [fs sn] in (e tt) in
        let g := context C [e] in
        let progname := fresh "prog" in
        set progname := g;
        change progname; unfold progname; clear progname
    | _ => 
        fail 1 "Failed to unfold program"
    end.
End ProgramTactic.

(* This tactic essentially just unfolds the definition of interpProgram.
   Because of typeclass complications, this cannot just be done with standard
   tactics. *)
Ltac unfold_program := ProgramTactic.unfold_program.

(*
Require Import spec spectac reg.
Require Import instrsyntax. Open Scope instr_scope.
Example exampleUnfoldLemma (i j: DWORD) p1  :
 i -- j :-> (LOCAL L;prog_skip;;L:;;p1;;INC EAX;;dd #4) |-- i -- j :-> p1.
Proof.
unfold_program.
sdestructs => i1 i2  -> i3 -> -> i4 i5.
rewrite -> memIsLe. sdestruct => H1.
rewrite -> memIsLe at 2. sdestruct => H1.
sbazooka.
Qed.
*)

Lemma programMemIs_entails_memAny (p: program) : forall i j,
  i -- j :-> p |-- memAny i j.
Proof. induction p => i j.
+ by apply readerMemIs_entails_memAny.
+ rewrite -> programMemIsSkip. sdestruct => ->. by apply memAnyEmpty.
+ rewrite programMemIsSeq. sdestruct => p'. rewrite -> IHp1.
rewrite -> IHp2. by apply memAnyMerge.
+ simpl. sdestruct => l. by rewrite -> H.
  rewrite -> programMemIsLabel.
  sdestructs => -> H. apply memAnyEmpty.
+ by apply readerMemIs_entails_memAny.
Qed.

Lemma ddApart p q (v:DWORD) : p -- q :-> dd v |-- apart 4 p q /\\ p -- q :-> dd v.
Proof. rewrite programMemIsData. apply memIsFixed. Qed.

Lemma dbApart p q (v:BYTE) : p -- q :-> db v |-- apart 1 p q /\\ p -- q :-> db v.
Proof. rewrite programMemIsData. apply memIsFixed. Qed.

Lemma dwApart p q (v:WORD) : p -- q :-> dw v |-- apart 2 p q /\\ p -- q :-> dw v.
Proof. rewrite programMemIsData. apply memIsFixed. Qed.

Lemma dsApart p q v : p -- q :-> ds v |-- apart (length v) p q /\\ p -- q :-> ds v.
Proof. rewrite programMemIsData. apply memIsFixed. Qed.

Lemma fixedSizePad n : fixedSizeReader (readPad n) n.
Proof.
induction n => //=.
+ by apply fixedSizeReader_retn.
+ by apply (fixedSizeReader_bind fixedSizeBYTE).
Qed.

Lemma padApart p q n : p -- q :-> pad n |-- apart n p q /\\ p -- q :-> pad n.
Proof. rewrite programMemIsData. apply fixedSizePad. Qed.


Definition hasSize n (pr: program) := forall p q, p -- q :-> pr |-- apart n p q /\\ p -- q :-> pr.

Lemma dbHasSize b : hasSize 1 (db b).
Proof. rewrite /hasSize. move => p q. apply dbApart. Qed.

Lemma dwHasSize b : hasSize 2 (dw b).
Proof. rewrite /hasSize. move => p q. apply dwApart. Qed.

Lemma ddHasSize b : hasSize 4 (dd b).
Proof. rewrite /hasSize. move => p q. apply ddApart. Qed.

Lemma padHasSize n : hasSize n ( pad n).
Proof. rewrite /hasSize. move => p q. apply padApart. Qed.

Lemma dsHasSize s : hasSize (length s) (ds s).
Proof. rewrite /hasSize. move => p q. apply dsApart. Qed.

Lemma seqHasSize p1 p2 n1 n2 : hasSize n1 p1 -> hasSize n2 p2 -> hasSize (n1+n2) (p1;;p2).
Proof. move => H1 H2 p q. rewrite programMemIsSeq. sdestructs => p'.
rewrite /hasSize in H1, H2. rewrite -> H1. rewrite -> H2.
sdestructs => A1 A2.
have A := (apart_addn A1 A2). sbazooka.
Qed.

Lemma localHasSize n f : (forall L, hasSize n (f L)) -> hasSize n (LOCAL L; f L).
Proof. move => H. rewrite /hasSize. move => p q. rewrite programMemIsLocal.
sdestruct => L. rewrite /hasSize in H. rewrite -> H. sbazooka.
Qed.

Lemma labelHasSize L : hasSize 0 (prog_label L).
Proof. rewrite /hasSize. move => p q. rewrite programMemIsLabel. sbazooka. Qed.



(*---------------------------------------------------------------------------
    Structural equivalence on programs, capturing monoidal sequencing and
    scope extrusion
  ---------------------------------------------------------------------------*)
Definition liftEq T U (eq: T -> T -> Prop) := fun (f g: U -> T) => forall u, eq (f u) (g u).
Inductive progEq : program -> program -> Prop :=
| progEqRefl:  forall p, progEq p p
| progEqSym:   forall p1 p2, progEq p1 p2 -> progEq p2 p1
| progEqTrans: forall p1 p2 p3, progEq p1 p2 -> progEq p2 p3 -> progEq p1 p3
| progEqDecLabel: forall p q, (liftEq progEq p q) -> progEq (prog_declabel p) (prog_declabel q)
| progEqSeq:   forall p1 p2 q1 q2, progEq p1 q1 -> progEq p2 q2 -> progEq (prog_seq p1 p2) (prog_seq q1 q2)
| progEqSeqAssoc: forall p1 p2 p3, progEq (p1;;p2;;p3) ((p1;;p2);;p3)
| progEqSeqSkip: forall p, progEq (p;;prog_skip) p
| progEqSkipSeq: forall p, progEq (prog_skip;;p) p
| progEqSeqDecLabel: forall p f, progEq (p;; prog_declabel f) (prog_declabel (fun l => p;; f l))
| progEqDecLabelSeq: forall p f, progEq (prog_declabel f;; p) (prog_declabel (fun l => f l;; p))
| progEqDecLabelSkip: progEq (prog_declabel (fun l => prog_skip)) prog_skip.

(* Add progEq as an instance of Equivalence for rewriting *)
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.RelationClasses.
Global Instance progEqEqu : Equivalence progEq.
Proof. constructor; red.
+ apply progEqRefl.
+ apply progEqSym.
+ apply progEqTrans.
Qed.

(* Declare morphisms for context rules *)
Global Instance progEq_seq_m:
  Proper (progEq ==> progEq ==> progEq) prog_seq.
Proof. move => p1 p2 EQ1 q1 q2 EQ2 . by apply progEqSeq. Qed.

Global Instance progEq_decLabel_m:
  Proper (liftEq progEq ==> progEq) prog_declabel.
Proof. move => f1 f2 EQ. by apply progEqDecLabel. Qed.


(* Main lemma: memIs respects progEq *)
Lemma memIsProgEquiv p1 p2 : progEq p1 p2 -> forall l l', mkCursor l -- mkCursor l' :-> p1 -|- mkCursor l -- mkCursor l' :-> p2.
Proof. move => EQ. induction EQ => l l'. 
(* progEqRefl *)
+ done.
(* progEqSym *)
+ by rewrite IHEQ.
(* progEqTrans *)
+ by rewrite IHEQ1 IHEQ2.
(* progEqDecLabel *)
+ unfold_program; unfold_program; split; sdestruct => lab; ssplit; [rewrite -> H0; reflexivity | rewrite <-H0; reflexivity ].
(* progEqSeq *)
+ unfold_program; unfold_program; split; sdestructs => i; [rewrite IHEQ1 IHEQ2; sbazooka | rewrite -IHEQ1 -IHEQ2; by sbazooka].
(* progEqSeqAssoc *)
+ unfold_program; unfold_program; by sbazooka.
(* progEqSeqSkip *)
+ unfold_program; unfold_program; sbazooka; by subst. 
(* progEqSkipSeq *)
+ unfold_program; unfold_program; sbazooka; by subst. 
(* progEqSeqDecLabel *)
+ do 3 rewrite /memIs/=. split; sbazooka.
(* progEqDecLabelSeq *)
+ do 3 rewrite /memIs/=. split; sbazooka.
(* progEqDecLabelSkip *)
+ unfold_program; unfold_program. split. sdestructs => i ->. by sbazooka. apply lexistsR with #0. by sbazooka.
Qed.

(* Now declare memIs as a morphism wrt progEq *)
Global Instance memIs_progEq_m (p p': ADDR):
  Proper (progEq ==> lequiv) (@memIs _ _ (mkCursor p) (mkCursor p')).
Proof. move => p1 p2 EQ. by apply memIsProgEquiv. Qed.
