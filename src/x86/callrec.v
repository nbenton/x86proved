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

Lemma toyfun_call_recAux (f:DWORD) P Q vs (i j:DWORD):
  |-- (|> toyfun f P Q -->> (safe @ (EIP ~= j ** Q) -->> safe @ (EIP ~= i ** P)) @ (retreg? ** stackinv vs)) @ (i -- j :-> call_toyfun f).
Proof. rewrite /call_toyfun. unfold_program. 
  autorewrite with push_at.
  specintros => i1 i2 i3 H1 H2. rewrite -H1 -H2.
  apply limplValid. rewrite /toyfun.
  autorewrite with push_later; last apply _. eapply lforallL.   
  autorewrite with push_at. 
  autorewrite with push_later; last apply _. eapply lforallL.

  (* pushcode *)
  superspecapply *. 
  (* JMP f *)
  superspecapply *. 
  autorewrite with push_at. 
  autorewrite with push_later; last apply _.
  cancel2.
  rewrite <- spec_later_weaken. finish_logic_with sbazooka. 
  finish_logic_with sbazooka. 
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

Lemma lobentails S : (|> S -->> S) |-- S.
apply spec_lob_context.
apply landAdj; reflexivity.
Qed.

(* now playing with recursion *)
Definition weakenContext (P Q:spec) : |-- Q -> P |-- Q.
Proof. move => H. by rewrite <- H. Qed. 

(* Example recursive function, with instructions nailed down *)
Definition exSpec f := Forall a b, toyfun f (EAX ~= a ** EBX ~= b) (EAX ~= #0 ** EBX ~= addB b a) @ OSZCP?.

(* Example recursive function *)
Definition toyfun_example_recursivecallee_program : program :=
  mkbody_toyfun (
  LOCAL L; LOCAL SKIP;
  L:;;
    INC EBX;;
    DEC EAX;;
    JZ SKIP;;
    call_toyfun L;;
  SKIP:;
  )%asm.

Theorem toyfun_example_correct_program (i1 i2:DWORD) :
  |-- exSpec i1 @ (i1 -- i2 :-> toyfun_example_recursivecallee_program).
Proof.
rewrite /toyfun_example_recursivecallee_program/mkbody_toyfun.

(* Do this BEFORE applying spec_lob or you will get in a mess with existentials *)
unfold_program. 
specintros => i3 i4 i5 i6 <- <- i7 i8 i9 i10 <- <- i11. 
(* Cleanup *)
rewrite empSPR empSPL 3!sepSPA. 

(* Now apply the Lob rule *)
apply spec_lob.

rewrite {2}/exSpec/toyfun. 
specintros => a b iret vs. 

(* Push non-code bit of frame inside *)
do 2 rewrite spec_at_impl. 

(* Pull out arbitrary flags and register *)
rewrite {7 8 9 10 11 12}/stateIsAny.
specintros => o s z c p r. simpl in o,s,z,c,p,a,r.

(* We want these unfolded in the rules *)
Hint Unfold OSZCP ConditionIs : specapply. 

(* INC EBX *)
superspecapply *. 

(* DEC EAX *)
superspecapply *. 

(* JZ SKIP *)
superspecapply *. 

specsplit. 
- (* Would be nice if we had a reflective tactic that did this *)
  setoid_rewrite <- spec_later_weaken at 2.
  specintros => /eqP/eqP EQ.  
  (* popcode *)
  specapply *. rewrite /stateIsAny. sbazooka.     
  (* JMP retreg *)
  superspecapply *. 
  (* usual stuff; should be able to automate this a bit *)
  apply weakenContext. rewrite <- spec_frame. apply limplValid. rewrite <- spec_later_weaken. 
  autorewrite with push_at. cancel1. rewrite /stateIsAny. sbazooka.  
  (* Arithmetic *)
  rewrite -{2}(decBK a). rewrite EQ incB_fromNat addB1. 
  by ssimpl. 

- specintros => /eqP ->. 
  rewrite /exSpec. 
  (* All this just to instantiate quantifiers on left of turnstile *)
     autorewrite with push_later; last apply _. rewrite spec_at_forall. apply lforallL with (decB a).
     autorewrite with push_later; last apply _. rewrite spec_at_forall. apply lforallL with (incB b).
     rewrite spec_at_toyfun.
   rewrite  -addB_decB_incB  decBK incBK.  
   
   set PRE := (EAX ~= decB _ ** _) ** _. 
   set POST := (EAX ~= #0 ** _) ** _.       
   instLem (@toyfun_call_rec i1 PRE POST (i1 -- i7 :-> (INC EBX)%asm**i7 -- i8 :-> (DEC EAX)%asm**i8 -- i9 :-> JZ%asm i10**i10 -- i11 :-> popcode**i11 -- i2 :-> JMP retreg)) => TFC. 

   (* call_toyfun L *)
   (* Have to rearrange in order to get frame right *)
   rewrite /toyfun in TFC.
   rewrite -> spec_at_impl in TFC.
   repeat rewrite ->(spec_at_at safe) in TFC.
   repeat rewrite -> (spec_at_at safe).
   rewrite /toyfun.
   rewrite spec_at_later.
      
   eapply (safe_safe_frame1 _).
   exact TFC. cancel1. specintros => iret' vs'. 
   rewrite spec_at_forall. apply lforallL with iret'. 
   rewrite spec_at_forall. apply lforallL with vs'. autorewrite with push_at. 
   cancel2. cancel1. sbazooka. cancel1. sbazooka.
   rewrite /ConditionIs/PRE/stateIsAny. split. sbazooka. sbazooka.

   apply weakenContext. rewrite {TFC}. 
   (* popcode *)
   rewrite /PRE/POST.
   superspecapply *. 
   (* JMP retreg *)
   superspecapply *. 
   (* Usual logic stuff *)
   setoid_rewrite <- spec_later_weaken. 
   rewrite /POST/PRE/stateIsAny. 
   finish_logic_with sbazooka.
Qed.

