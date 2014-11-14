Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spectac x86proved.spec x86proved.safe x86proved.pointsto x86proved.cursor x86proved.x86.instr.
Require Import x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.instrsyntax x86proved.x86.macros x86proved.x86.instrrules.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import x86proved.common_tactics x86proved.basicspectac x86proved.chargetac.

Definition retreg := EBP.

(* Check (#3 :-> [:: #0; #1 ]). *)

Definition pushcode (c: DWORD) := PUSH c.  
Definition stackinv (vs: seq DWORD) := Exists sp:DWORD, ESP ~= sp ** sp :-> vs.  

Axiom pushaxiom : forall v vs, |-- basic (stackinv vs) (pushcode v) (stackinv (v::vs)).
Global Instance: forall v, instrrule (pushcode v) := @pushaxiom. 

Definition popcode : program := POP retreg.
Axiom popaxiom : forall vs v, |-- basic (stackinv (v::vs) ** retreg?) popcode (retreg~=v ** stackinv vs).
Global Instance: instrrule popcode := @popaxiom.

(* Toy function calling convention *)
Definition toyfun f P Q :=
  Forall (iret:DWORD), Forall vs, (safe @ (EIP~=iret ** stackinv vs ** Q)
          -->> safe @ (EIP~=f ** stackinv (iret::vs) ** P)) @ retreg?.

(* Use this macro for calling f *)
Definition call_toyfun f :=
  (LOCAL iret;
    pushcode iret;;
    JMP f;;
  iret:;)
  %asm.

(* Use this macro to make a function that returns in the end *)
Definition mkbody_toyfun (p: program) :=
  p;; popcode ;; JMP retreg.

(* It's useful to define local functions *)
Notation "'let_toyfun' f  ':=' p 'in' q" :=
  (LOCAL skip; JMP skip;; LOCAL f; f:;; mkbody_toyfun p;; skip:;; q)%asm
  (at level 45, f ident, right associativity).


(* Example recursive function *)
Definition toyfun_example_recursivecallee : program :=
  mkbody_toyfun (
  LOCAL L; LOCAL SKIP;
  L:;;
    INC EBX;;
    DEC EAX;;
    JZ SKIP;;
    call_toyfun L;;
  SKIP:;
  )%asm.


Lemma spec_at_toyfun f P Q R:
  toyfun f P Q @ R -|- toyfun f (P**R) (Q**R).
Proof.
  rewrite /toyfun.
  autorewrite with push_at.  cancel1 => iret.
  autorewrite with push_at.
  cancel1 => vs.
  autorewrite with push_at. split; cancel2; cancel1; ssimpl. 
Qed.
Hint Rewrite spec_at_toyfun : push_at.

Lemma basic_seq_frame (c1 c2: program) S P Q R F:
  S |-- basic P c1 Q @ F ->
  S |-- basic Q c2 R @ F ->
  S |-- basic P (c1;; c2) R @ F.
Proof.
  move=> Hc1 Hc2. rewrite spec_at_basic. eapply basic_seq. 
  rewrite ->spec_at_basic in Hc1. apply Hc1.  
  rewrite ->spec_at_basic in Hc2. apply Hc2.  
Qed.  

Lemma basic_local_frame S P c Q R:
  (forall l, S |-- (basic P (c l) Q @ R)) ->
  S |-- basic P (prog_declabel c) Q @ R.
Proof.
  rewrite ->spec_at_basic. move => H. apply basic_local => l. specialize (H l). by rewrite ->spec_at_basic in H.  
Qed. 

Lemma toyfun_call (f:DWORD) P Q vs:
  |> toyfun f P Q |-- basic P (call_toyfun f) Q @ (retreg? ** stackinv vs).
Proof.
  rewrite /call_toyfun. 
  apply basic_local_frame => iret. 
  rewrite -spec_at_at spec_at_swap spec_at_basic. 
  apply: basic_seq_frame. 
  basic apply pushaxiom. 
  rewrite /basic. specintros => i j. unfold_program. specintros => *; do !subst.

  rewrite spec_at_swap. rewrite spec_at_impl. 
  superspecapply *.

  rewrite <- (spec_frame (i -- iret :-> JMP f)). rewrite /toyfun. autorewrite with push_at.
  apply limplAdj. apply landAdj.
  
  autorewrite with push_later; last apply _. 
  rewrite spec_at_later.
  autorewrite with push_later. eapply lforallL.
  autorewrite with push_later; last apply _. autorewrite with push_at. eapply lforallL.   
  autorewrite with push_at. autorewrite with push_later; last apply _.
  cancel2. rewrite <- spec_later_weaken. finish_logic_with sbazooka. finish_logic_with sbazooka. 
Qed.

Lemma toyfun_call_recAux (f:DWORD) P Q vs (i j:DWORD):
  |-- (|> toyfun f P Q -->> (safe @ (EIP ~= j ** Q) -->> safe @ (EIP ~= i ** P)) @ (retreg? ** stackinv vs)) @ (i -- j :-> call_toyfun f).
Proof. rewrite /call_toyfun. unfold_program. 
  autorewrite with push_at.
  specintros => i1 i2 i3 H1 H2. rewrite -H1 -H2.
  apply limplValid. rewrite /toyfun.
  autorewrite with push_later; last apply _. eapply lforallL.   
  autorewrite with push_at. 
  autorewrite with push_later; last apply _. eapply lforallL.

  superspecapply pushaxiom.
  superspecapply JMP_I_rule. autorewrite with push_at. 
  autorewrite with push_later; last apply _.
  cancel2.
  rewrite <- spec_later_weaken. cancel1. sbazooka.
  cancel1. sbazooka. 
Qed.

Corollary toyfun_call_rec (f:DWORD) P Q R vs (i j:DWORD):
 |> toyfun f P Q @ (i -- j :-> call_toyfun f ** R)  |-- (safe @ (EIP ~= j ** Q) -->> safe @ (EIP ~= i ** P)) @ (retreg? ** stackinv vs) @ (i -- j :-> call_toyfun f ** R).
Proof.
apply limplValid. rewrite <- spec_at_later. rewrite <- spec_at_impl. 
rewrite <-spec_at_at. rewrite <- spec_frame. apply toyfun_call_recAux. 
Qed. 

Lemma toyfun_mkbody (f f': DWORD) P p Q:
  (Forall vs, basic P p Q @ (stackinv vs)) |--
    toyfun f P Q @ (f--f' :-> mkbody_toyfun p).
Proof.
  rewrite /toyfun. specintro => iret. rewrite /mkbody_toyfun.
  unfold_program. specintros => i1 i' vs.
  eapply lforallL with (iret :: vs).

  (* This is a bit hairy *)
  autorewrite with push_at. 
  apply limplAdj. 
  eapply (safe_safe_context _); first reflexivity. apply landL1. 
  do 2 eapply lforallL. reflexivity. by ssimpl.  

  superspecapply *.
  superspecapply *. rewrite <-spec_later_weaken.  
  finish_logic_with sbazooka.  
Qed.

(* the following shows we didn't need that stackinv in there above (could have framed it anyway)
   not immediately clear to me which version one actually wants
*)
Lemma toyfun_mkbody' (f f': DWORD) P p Q:
  basic (P) p (Q)  |--
    toyfun f P Q @ (f--f' :-> mkbody_toyfun p).
Proof.
  rewrite /toyfun. specintro => iret. rewrite /mkbody_toyfun.
  unfold_program. specintros => i1 i' vs.
   
  autorewrite with push_at. 
  apply limplAdj. 
  eapply (safe_safe_context _); first reflexivity. apply landL1.
  do 2 eapply lforallL. reflexivity. 
  by ssimpl.  

  superspecapply *.
  superspecapply *. rewrite <-spec_later_weaken. 
  finish_logic_with sbazooka. 
Qed.

Lemma lobentails S : (|> S -->> S) |-- S.
apply spec_lob_context.
apply landAdj; reflexivity.
Qed.

(* now playing with recursion *)
Lemma lobunderAt (f:DWORD) P Q p f' : (|-- (|> toyfun f P Q -->> toyfun f P Q) @ (f -- f' :-> mkbody_toyfun p)) -> (|-- toyfun f P Q @ (f -- f' :-> mkbody_toyfun p)).
move => H.
apply spec_lob_context. apply landL2. apply limplValid. autorewrite with push_at in H. 
autorewrite with push_at. assumption. 
Qed.

Lemma rocov S S' R : S |-- S' -> S @ R |-- S' @ R.
move => H.
rewrite <-H.
reflexivity.
Qed.

(* arggh, different levels of entailment are really vexing *)
Lemma lobunderAt' (f:DWORD) P Q p f' : ((|> toyfun f P Q -->> toyfun f P Q) @ (f -- f' :-> mkbody_toyfun p)) |-- (toyfun f P Q @ (f -- f' :-> mkbody_toyfun p)).
apply rocov.
apply lobentails.
Qed.

(* possibly an easier way to do that! *)

Lemma toyfun_mkbody_context S (f f': DWORD) P p Q:
  S //\\ basic P p Q  |--
  (S -->>  toyfun f P Q) @ (f--f' :-> mkbody_toyfun p).
Proof.
  rewrite /toyfun. specintro => iret. rewrite /mkbody_toyfun. 
  unfold_program. autorewrite with push_at.
  specintros => vs i1 i'.

  apply limplAdj. autorewrite with push_at.  
  apply limplAdj. 
  eapply (safe_safe_context _); first reflexivity. apply landL1. apply landL1.
  apply landL2. do 2 eapply lforallL. reflexivity. 
  by ssimpl. 

  superspecapply *.
  superspecapply *. rewrite <- spec_later_weaken.
  finish_logic_with sbazooka. 
Qed.



(* Now, as a special case of the above, we can define singly-recursive functions 
   But note that this actual form of definition is rarely going to be useful as it
   bakes in a particular P and Q, which will only be any use for trivial functions - we'll
   usually want some quantification and adaptation in there
*)
Lemma toyfun_mkbody_rec (f f': DWORD) P p Q:
  |> toyfun f P Q //\\ basic P p Q  |--
  (toyfun f P Q) @ (f--f' :-> mkbody_toyfun p).
Proof.
rewrite <-lobunderAt'. apply toyfun_mkbody_context.  
Qed.

(*
   Example that shows a caller and a callee independently verified and then
   composed.
 *)

Definition exSpec f := Forall a b, toyfun f (EAX ~= a ** EBX ~= b) (EAX ~= #0 ** EBX ~= addB b a) @ OSZCP?.
Example toyfun_example_body_correct (f f': DWORD):
  |-- (|> exSpec f -->> exSpec f) @ (f -- f' :-> toyfun_example_recursivecallee).
Proof.  
  rewrite /toyfun_example_recursivecallee/mkbody_toyfun. (*unfold_program.*)
  rewrite {2}/exSpec. 
  specintros => a b. 
  rewrite /toyfun.
  specintros => iret vs.
  rewrite spec_at_impl. 
  rewrite spec_at_impl.
  rewrite spec_at_impl. 

(*  specintro => i1. specintro => i2 i3 i4 <- <- i5 i6 i7 i8 <- <- i9. *)
  rewrite /stateIsAny.
  specintros => o s z c p r.
  simpl in o,s,z,c,p,a,r.

  apply limplValid. 

  (* Why do we need this? Answer: because specapply doesn't unfold stuff in rules in contrast to basic apply  *)
  (* INC EBX *)
  unfold_program. unfold_program.
  specintros => i1 i2 i3 i4 <- <- i5 i6 i7 i8 <- <- i9.
  instrrule pose (INC_R_rule (r:=EBX)) as RULE.
  rewrite /OSZCP in RULE. rewrite spec_at_at. 
  superspecapply RULE. clear RULE.

  (* DEC EAX *)
  instLem (DEC_R_rule (r:=EAX)) => RULE. 
  rewrite /OSZCP in RULE.
  superspecapply RULE. clear RULE. 

  (* JZ SKIP *)
  superspecapply JZ_rule. 
  specsplit. 
  - setoid_rewrite <- spec_later_weaken at 2. specintros => H.
    specapply popaxiom. 
      rewrite /stateIsAny. sbazooka. 
    superspecapply *. setoid_rewrite <- spec_later_weaken at 2. 
    autorewrite with push_at.
    finish_logic. apply landL2. cancel1. sbazooka.
    rewrite -{2}(decBK a).  
    rewrite (eqP (eqP H)). rewrite incB_fromNat addB1. by ssimpl. 

 - specintros => H. rewrite (eqP H).  
   rewrite /exSpec. 
     autorewrite with push_later; last apply _. rewrite spec_at_forall. apply lforallL with (decB a).
     autorewrite with push_later; last apply _. rewrite spec_at_forall. apply lforallL with (incB b).
     rewrite spec_at_toyfun.
   set PRE := (EAX ~= decB _ ** _) ** _. 
   rewrite  -addB_decB_incB  decBK incBK.  
   set POST := (EAX ~= #0 ** _) ** _.       
   
   set I1 := (f -- i5 :-> _). 
   set I2 := (i5 -- i6 :-> _). 
   set I3 := (i6 -- i7 :-> _). 
   set I4 := (i8 -- i9 :-> _). 
   set I5 := (i9 -- f' :-> _). 
   instLem (@toyfun_call_rec f (PRE) (POST) (I1**I2**I3**I4**I5)) => TFC.
   unfold I1, I2, I3, I4, I5 in *.

   
   (* call_toyfun L *)
   (* Have to rearrange in order to get frame right *)
(*   rewrite -> (spec_at_swap _ (_ -- _ :-> call_toyfun f)) in TFC. *)
   rewrite -> spec_at_impl in TFC. 
   do 2 rewrite -> (spec_at_at safe) in TFC.
   rewrite /toyfun in TFC.
   (* But now we do at least get to use specapply *)
   specapply TFC; last first.

   (* popcode *)
   rewrite /PRE/POST.
   superspecapply popaxiom. 
   (* JMP retreg *)
   superspecapply *. 
   (* Usual logic stuff *)
   setoid_rewrite <- spec_later_weaken at 2. autorewrite with push_at. 
   apply limplAdj. apply landL2. 
   rewrite /POST/stateIsAny. cancel1. sbazooka. 
   rewrite /PRE/stateIsAny. sbazooka.


   (* Now the remaining obligation from specapply TFC. *)
   autorewrite with push_later; last apply _. rewrite /toyfun. 
   autorewrite with push_at. specintros => iret'. 
   autorewrite with push_at. cancel1. 
   specintros => vs'. apply lforallL with iret'. rewrite spec_at_forall. 
   apply lforallL with vs'. 
   rewrite spec_at_at. rewrite spec_at_at.
   autorewrite with push_at. cancel2. cancel1. admit.  cancel1. sbazooka. 
Qed.

Corollary toyfun_example_correct (f f': DWORD):
  |-- exSpec f @ (f--f' :-> toyfun_example_recursivecallee).
Proof.
apply spec_lob. apply limplValid. rewrite <-spec_at_later. 
rewrite <- spec_at_impl. apply toyfun_example_body_correct. 
Qed. 

