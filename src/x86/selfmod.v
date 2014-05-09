Require Import ssreflect ssrbool ssrnat eqtype tuple seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic program.
Require Import instr instrsyntax instrrules reader pointsto cursor.
Require Import triple monad eval instrcodec enc encdechelp basicprog.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Lemma jmpBytes (i1 i2 i': DWORD) (p: program) (bytes : seq BYTE) :
  i' :-> bytes |-- i' :-> p 
->
  |-- ((|> safe @ (i' :-> p ** EIP ~= i')) -->> 
           safe @ (i' :-> bytes ** EIP ~= i1)) <@ (i1 -- i2 :-> JMP i').
Proof. move => H1.
rewrite -> H1. 
specapply JMP_I_rule.  
sbazooka. autorewrite with push_at. rewrite <- spec_reads_frame. apply limplValid. 
cancel1. cancel1. sbazooka. 
Qed. 

Lemma jmpBytes_basic (i j:DWORD) p (bytes: seq BYTE) P :
  i -- j :-> bytes |-- i -- j :-> p ->
  |-- safe @ (EIP ~= i ** P) <@ (i -- j :-> p) -> (*basic P p Q ->*)
  |-- Forall i1, Forall j1:DWORD, (|> safe @ (EIP ~= i1 ** P)) <@ (i1 -- j1 :-> JMP i ** i -- j :-> bytes).
Proof. move => H1 H2.
specintros => i1 j1.
specapply JMP_I_rule. sbazooka.
rewrite <- spec_reads_frame. 
autorewrite with push_at.
apply limplValid. cancel1. 
Qed. 

Lemma inlineBytes (i: DWORD) (p: program) (bytes: seq BYTE) :
  i :-> bytes |-- i :-> p ->
  |-- safe @ (i :-> p ** EIP ~= i) -->>
      safe @ (i :-> bytes ** EIP ~= i).
Proof. move => H. 
rewrite -> H.
apply limplValid. cancel1.
Qed. 

(* Self-modifying code!
   Effect is PUSH r
*)
Definition selfModImp r (v: DWORD) : program :=
LOCAL PUSHCONST;
  MOV EDI, PUSHCONST;;
  MOV [EDI], r;;
  db #x"68";;
PUSHCONST:;;
  dd v.

Lemma interpReader_letSplit2 T m n (v:_) (r: _ -> _ -> Reader T) : 
  interpReader (let (x,y) := split2 n m v in r x y) = interpReader (r (high n v) (low m v)).
Proof. done.  Qed. 

Hint Rewrite interpReader_bind interpReader_retn interpReader_letPair interpReader_letSplit2 : INTERP. 
Ltac SOLVE :=  
  try repeat (try autorewrite with INTERP; try (sdestructs; intros); try discriminate).

Ltac CASESOLVE := 
  (let E := fresh "E" in case E: (_ == _); try rewrite (eqP E); clear E; SOLVE).

(* Extremely long-winded way of showing this! *)
Lemma PUSH_decoding (p addr: DWORD) q : 
p -- q :-> PUSH addr -|- 
  (p :-> #x"68" ** next p -- q :-> addr) \\// 
  (Exists b, signTruncate _ (n:=7) addr = Some b /\\ p :-> #x"6A" ** next p -- q :-> b).
Proof. 
split. 
(* => *)
rewrite /pointsTo{1}/memIs/readerMemIs/readNext/readInstr/readNext. 
(*apply lexistsL => q.*)
rewrite -> interpReader_bindBYTE. 
apply lexistsL => b. rewrite <-pointsToBYTE_byteIs. 
rewrite /pointsTo. sdestruct => p'. rewrite -> memIsBYTE_next_entails. 
sdestruct => H. subst. 

CASESOLVE. 
CASESOLVE. 
CASESOLVE. 
CASESOLVE. 
CASESOLVE. 
CASESOLVE. 
CASESOLVE. 
CASESOLVE. 
CASESOLVE. 
CASESOLVE.
CASESOLVE.

(* It is #x"68" *)
rewrite {3}/memIs.
apply lorR1. sbazooka. injection x2 => ->. 
subst. reflexivity. 

(* Test for #x"6A" *)
CASESOLVE.
(* It is #x"6A" *)
apply lorR2. 
injection x2 => <-. 
sbazooka.
by rewrite signExtendK. 
rewrite {3}/memIs/readerMemIs. sbazooka. subst. reflexivity.

(* It's neither #x"68" nor #x"6A" *)
do 10 CASESOLVE. 
do 10 CASESOLVE. 
do 11 CASESOLVE. 
destruct x0.
destruct r;  SOLVE. 
do 10 CASESOLVE. 

(* <= *)
(*rewrite {2}/pointsTo {1}/memIs/readerMemIs/readNext/readInstr. *)
apply lorL.

(* 68 *)
rewrite pointsToBYTE_byteIs.
rewrite {2}/memIs/readerMemIs/readNext/readInstr.
rewrite -> interpReader_bindBYTE.
apply lexistsR with #x"68". 
ssimpl. 
try replace (_ == _) with false by done.
try replace (_ == _) with false by done.
try replace (_ == _) with true by done.
rewrite -> interpReader_bind.
apply lexistsR with q.
apply lexistsR with addr. 
rewrite -> interpReader_retn.
sbazooka. reflexivity. 

(* 6A *)
sdestructs => b SMALL. 
rewrite {2}/memIs/readerMemIs/readNext/readInstr.
rewrite -> interpReader_bindBYTE.
apply lexistsR with #x"6A". 
rewrite pointsToBYTE_byteIs.
ssimpl. 
try replace (_ == _) with false by done.
try replace (_ == _) with false by done.
try replace (_ == _) with false by done.
try replace (_ == _) with true by done.
rewrite -> interpReader_bind.
apply lexistsR with q.
apply lexistsR with b. 
rewrite -> interpReader_retn.
rewrite /memIs/readNext. 
rewrite (signTruncateK SMALL).
sbazooka. 
Qed. 

(*
Lemma MOV_PUSH_R_rule (p: DWORD) (r1 r2: Reg) (v1 v2:DWORD) :
  |-- basic (r1~=p ** p :-> #x"68" ** next p :-> v1 ** r2~=v2)
            (MOV [r1 + 1], r2)
            (r1~=p ** p :-> PUSH v2 ** r2~=v2).
Proof.
  rewrite PUSH_decoding => //. 
  have RULE:= (MOV_MR_rule (offset:=1) (r1:=r1) (r2:=r2) (p:=p) (v1:=v1) (v2:=v2)).
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV. 
  triple_apply triple_letGetRegSep.
  triple_apply evalMemSpecNone_rule. 
  triple_apply triple_setDWORDSep.
Admitted.  (*apply lorR1. 
  sbazooka. 
  reflexivity. 
Qed.*)

*)

Lemma dbDef (p:DWORD) q b : p -- q :-> db b -|- q = next p /\\ p :-> b. 
Proof. split. 
+ simpl. sdestructs => b' -> <-. rewrite pointsToBYTE_byteIs. sbazooka. 
+ simpl. apply lexistsR with b. rewrite pointsToBYTE_byteIs. sbazooka. 
Qed. 

Lemma ddDef (p:DWORD) (d:DWORD) : p :-> dd d -|- p :-> d. 
Proof. rewrite /dd/pointsTo. 
split. 
+ sdestruct => q. unfold_program. apply lexistsR with q. reflexivity. 
+ sdestruct => q. apply lexistsR with q. unfold_program. reflexivity.  
Qed. 

Lemma ddDefAux p q (d:DWORD) : p -- q :-> dd d -|- p -- q :-> d. 
Proof. rewrite /dd. unfold_program. reflexivity. Qed. 


Corollary PUSH_DWORD_decoding (p addr: DWORD) j : 
  p :-> (#x"68":BYTE) ** next p -- j :-> addr |-- p -- j :-> PUSH addr.
Proof. rewrite ->PUSH_decoding. apply lorR1. reflexivity. Qed. 

(* A version of the PUSH_I rule in which the encoding is spelt out explicitly using
   data directives *)
Lemma PUSH_I_BYTES_rule (sp v w:DWORD) :
  |-- basic (ESP ~= sp    ** sp-#4 :-> w) 
            (db #x"68";; dd v)
            (ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. 
rewrite /basic. 
specintros => i j. 
unfold_program. 
specintros => i1. rewrite -> dbDef. 
specintros => ->. rewrite -> ddDefAux. 
rewrite -> PUSH_DWORD_decoding.
specapply PUSH_I_rule.
sbazooka. autorewrite with push_at. 
rewrite <- spec_reads_frame. 
apply limplValid. cancel1. sbazooka. 
Qed. 

Lemma MOV_M0R_ruleAux (pd:BITS 32) pe (r1 r2:Reg) (v1 v2: DWORD) :
  |-- basic (r1 ~= pd ** pd -- pe :-> v1 ** r2 ~= v2)
            (MOV [r1], r2)
            (r1 ~= pd ** pd -- pe :-> v2 ** r2 ~= v2).
Proof. rewrite -> memIsFixed. specintros => ->. 
basicapply MOV_M0R_rule. rewrite -> memIs_pointsTo. sbazooka. 
rewrite /pointsTo. sdestruct => q. 
rewrite -> memIsFixed. sdestruct => ->. sbazooka. 
Qed. 

Lemma modPUSH (r:Reg) (v w: DWORD) j2:
  |-- Forall i, Forall j1, 
      (safe @ (EIP ~= j1 ** j1 :-> #x"68" ** j1+#1 -- j2 :-> v ** EDI ~= j1+#1 ** r ~= v) -->>
      (safe @ (EIP ~= i **  j1 :-> #x"68" ** j1+#1 -- j2 :-> w ** EDI ~= j1+#1 ** r ~= v))) <@
      (i -- j1 :-> MOV [EDI], r).
Proof. 
specintros => i j1.
specapply
  (MOV_M0R_ruleAux(pd := j1 +# 1) (pe := j2) (r1 := EDI) (r2 := r) (v1 := w) (v2 := v)).
sbazooka.
rewrite <- spec_reads_frame. 
autorewrite with push_at. 
apply limplValid. cancel1.
sbazooka. 
Qed. 

Lemma modPUSHAux (r:Reg) (v w: DWORD) j2:
  |-- Forall i, Forall j1, 
      (safe @ (EIP ~= j1 ** j1+#1 -- j2 :-> v) -->>
      (safe @ (EIP ~= i **  j1+#1 -- j2 :-> w))) @ (EDI ~= j1+#1 ** r~=v) <@
      (i -- j1 :-> (MOV [EDI], r) ** j1 :-> #x"68").
Proof. 
specintros => i j1.
specapply
  (MOV_M0R_ruleAux(pd := j1 +# 1) (pe := j2) (r1 := EDI) (r2 := r) (v1 := w) (v2 := v)).
sbazooka.
rewrite <- spec_reads_frame. 
autorewrite with push_at. 
apply limplValid. cancel1.
sbazooka. 
Qed. 

Lemma TRIPLE_mysafe instr P Q (i j: DWORD):
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) (Q ** R)) ->
  |-- (|> safe @ Q -->> safe @ (EIP ~= i ** P)) @ (i -- j :-> instr).
Proof.
  move=> H. autorewrite with push_at.
  rewrite sepSPA. apply limplValid.
  specialize (H (i -- j :-> instr)). admit. 
Qed.

Lemma TRIPLE_mybasic instr P Q:
  (forall (R: SPred), TRIPLE (P ** R) (evalInstr instr) (Q ** R)) ->
  |-- Forall i, Forall j, (safe @ (EIP ~= i ** Q) -->> safe @ (EIP ~= j ** P)) 
      @ (j -- i :-> instr).
Proof.
  move=> H. specintros => i j.
  rewrite ->(spec_later_weaken (safe @ (EIP~=i ** Q))).
  apply TRIPLE_mysafe => R. triple_apply H.
Qed.


Lemma PUSH_rule src sp (v:DWORD) :
  |-- specAtSrc src (fun w => 
      Forall i, Forall j, 
      (safe @ (EIP ~= i ** ESP ~= sp-#4 ** sp-#4 :-> w) -->>
       safe @ (EIP ~= j ** ESP ~= sp ** sp-#4 :-> v)) @ (j -- i :-> PUSH src)).  
Proof.
admit. 
Qed. (*rewrite /specAtSrc. destruct src.
- apply TRIPLE_mybasic => R.
  rewrite /evalInstr/evalSrc. 
  rewrite -> id_l.
  triple_apply evalPush_rule. 
- elim: ms => [base indexAndScale offset]. 
  case: indexAndScale => [[rix sc] |]. 
  rewrite /specAtMemSpec.
  + specintros => oldv pbase indexval. 
    autorewrite with push_at. apply TRIPLE_mybasic => R.
    autounfold with eval. rewrite /evalSrc. 
    triple_apply evalMemSpec_rule. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalPush_rule. 
  + rewrite /specAtMemSpec. specintros => oldv pbase.
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc.
    triple_apply evalMemSpecNone_rule. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalPush_rule. 

- specintros => oldv. 
  autorewrite with push_at. 
  apply TRIPLE_basic => R. 
  rewrite /evalInstr.
  triple_apply triple_letGetRegSep.
  triple_apply evalPush_rule. 
Qed. 
*)

(*
Lemma basicWeaken P c Q :
  (forall i j, |--    (safe @ (EIP~=j ** P) -->>
          safe @ (EIP~=i ** Q)) <@
         (i -- j :-> c)) ->
  |--Forall i,
     Forall j,
         (safe @ (EIP~=j ** P) -->>
          safe @ (EIP~=i ** Q)) @
         (i -- j :-> c).
Proof. move => H. 
specintros => i j. specialize (H i j). 
rewrite -> spec_reads_impl in H. 
rewrite <- spec_at_entails_reads in H. 
rewrite <- spec_at_reads in H. apply: H. specintros. 
rewrite -> spec_at_entails_reads in H. 
autorewrite with push_at in H. 
specintros => i j. autorewrite with push_at. rewrite spec_reads_frame in H. apply H.   
*)

 Lemma my_at P Q R :
    (safe @ P -->> safe @ Q) @ R |-- (safe @ (P ** R) -->> safe @ (Q ** R)).  
  Proof.
    autorewrite with push_at. cancel1.  
  Qed.     

Lemma modPushAndDoIt (r:Reg) (v w: DWORD) j2 sp:
  |-- Forall i, Forall j1,
      (safe @ (EIP ~= j2 ** j1+#1 -- j2 :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v) -->>
      (safe @ (EIP ~= i **  j1+#1 -- j2 :-> w ** ESP ~= sp    ** sp-#4 :-> w))) @ (EDI ~= j1+#1 ** r~=v ** j1 :-> #x"68") <@
      (i -- j1 :-> (MOV [EDI], r)).
Proof. specintros => i j1. 

specapply
  (MOV_M0R_ruleAux(pd := j1 +# 1) (pe := j2) (r1 := EDI) (r2 := r) (v1 := w) (v2 := v)).
sbazooka.
rewrite <- spec_reads_frame.
autorewrite with push_at.  
rewrite spec_at_at. (*autorewrite with push_at. *)
Locate eq_pred.
rewrite <- spec_at_at.
rewrite <- spec_at_at.
cancel1.
sbazooka. 
have M := (my_at (R := (j1 +# 1 -- j2 :-> v))). 
autorewrite with push_at. rewrite -> my_at. apply my_at. cancel1. apply (my_at (R := (j1 := #x. 
Admitted.


Lemma modPushAndDoItAux (r:Reg) (v w: DWORD) j2 sp:
  |-- Forall i, Forall j1,
      (safe @ (EIP ~= j2 ** ESP ~= sp-#4 ** sp-#4 :-> v) -->>
      (safe @ (EIP ~= i **  ESP ~= sp    ** sp-#4 :-> w))) 
      @ (EDI ~= j1+#1 ** r~=v) <@
      (Exists d:DWORD, i -- j1 :-> (MOV [EDI], r) ** j1 :-> #x"68" ** (j1+#1) -- j2 :-> d).
Proof. specintro => i. specintro => j1. 
specintros => d.  => specapply
  (MOV_M0R_ruleAux(pd := j1 +# 1) (pe := j2) (r1 := EDI) (r2 := r) (v1 := w) (v2 := v)).
sbazooka.
rewrite <- spec_reads_frame. 


Lemma selfModPUSH_R_rule (r:Reg) sp (v w:DWORD) i j :
  |-- safe @ (EDI? ** r ~= v ** ESP ~= sp-#4 ** sp-#4 :-> v ** i -- j :-> (db #x"68";;
  dd v)) -->> 
      safe @ (EDI? ** r ~= v ** ESP ~= sp ** sp-#4 :-> w ** i -- j :-> (db #x"68";; dd #0)).
Proof. have PIB := PUSH_I_BYTES_rule. 
specialize (PIB sp v w).
rewrite /basic in PIB. 
rewrite limplAdj in PIB.
rewrite spec_reads_entails_at in PIB. 
specapply PIB. PUSH_I_BYTES_rule. sbazooka. 

Proof. rewrite /selfModImp. 
apply basic_local => L. 
eapply basic_seq. basicapply (MOV_RI_rule).
eapply basic_seq.  
basicapply MOV_MR_rule. rewrite /basic. 
specintros => i j.
unfold_program. 
specintros => i1 i2 -> -> i3. 
rewrite dbDef. specintros => ->. rewrite -> ddDefAux.
rewrite empSPL.

rewrite (sepSPC (i -- L :-> _)).
rewrite <- spec_reads_merge.
rewrite <- spec_reads_split. apply MOV_MR_rule.
sbazooka. 
autorewrite with push_at.
rewrite <- spec_reads_impl.
rewrite spec_reads_swap.
specapply MOV_MR_rule.
specapply MOV_MR_rule.
ssimpl. 

rewrite ->(PUSH_DWORD_decoding C). 
rewrite {3}sepSPA. (i -- L :-> (MOV [EEI.
specapply MOV_MR_rule.
sbazooka. ssimpl. rewrite <- spec_at_entails_reads. 
autorewrite with push_at. 
specapply (inlineBytes (PUSH_DWORD_decoding (p:= L) (addr := v))). 

autorewrite with push_at. 
setoid_rewrite -> ddDef.
(* Problem here is that <@ doesn't permit changes to code *)
specapply (MOV_MR_rule). sbazooka. ; first last.
rewrite <- spec_reads_frame.
autorewrite with push_at. apply limplValid. cancel1. 
ssimpl. 
rewrite /regAny. sbazooka.  ssimpl. apply: landL2.  autorewrite with push_at. rewrite <- spec_later_weaken. 
sbazooka. reflexivity. plit. 
ssimpl.  sbazooka. rewrite / sbazooka. Qed. 

