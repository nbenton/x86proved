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

Lemma lobentails S : (|> S -->> S) |-- S.
apply spec_lob_context.
apply landAdj; reflexivity.
Qed.

(* now playing with recursion *)
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
unfold toyfun_example_recursivecallee_program.
rewrite /mkbody_toyfun.

(* Do this BEFORE applying spec_lob or you will get in a mess with existentials *)
unfold_program. 
specintros => i3 i4 i5 i6 <- <- i7 i8 i9 i10 <- <- i11. rewrite empSPR empSPL 3!sepSPA. 

apply spec_lob.
  rewrite {2}/exSpec. 
  specintros => a b. 
  rewrite /toyfun.
  specintros => iret vs.
  
  rewrite spec_at_impl. 
  rewrite spec_at_impl.
  rewrite spec_at_impl. 

  rewrite {7 8 9 10 11 12}/stateIsAny.
  specintros => o s z c p r.
  simpl in o,s,z,c,p,a,r.

  (* INC EBX *)
  specapply *. rewrite /OSZCP. ssimpl.

  (* DEC EAX *)
  specapply *. rewrite /OSZCP. ssimpl.

  (* JZ SKIP *)
  specapply *. rewrite /OSZCP/ConditionIs. ssimpl.

  specsplit. 
  - setoid_rewrite <- spec_later_weaken at 2.
    specintros => H.
    specapply popaxiom. rewrite /ConditionIs. rewrite /stateIsAny. sbazooka.     
    superspecapply *. 
    finish_logic. apply landL2. rewrite <- spec_later_weaken. cancel1.
    rewrite (eqP H).  sbazooka.  rewrite -{2}(decBK a). rewrite (eqP (eqP H)). rewrite incB_fromNat. rewrite addB1. 
    by ssimpl. 

 - specintros => H. rewrite (eqP H).  
   rewrite /exSpec. 
     autorewrite with push_later; last apply _. rewrite spec_at_forall. apply lforallL with (decB a).
     autorewrite with push_later; last apply _. rewrite spec_at_forall. apply lforallL with (incB b).
     rewrite spec_at_toyfun.
   set PRE := (EAX ~= decB _ ** _) ** _. 
   rewrite  -addB_decB_incB  decBK incBK.  
   set POST := (EAX ~= #0 ** _) ** _.       
   
   instLem (@toyfun_call_rec i1 PRE POST
     (i1 -- i7 :-> (INC EBX)%asm**i7 -- i8 :-> (DEC EAX)%asm**i8 -- i9 :-> JZ%asm i10**i10 -- i11 :-> popcode**i11 -- i2 :-> JMP retreg)) => TFC. 

   (* call_toyfun L *)
   (* Have to rearrange in order to get frame right *)
   rewrite /toyfun in TFC.
   rewrite -> spec_at_impl in TFC.
   rewrite ->(spec_at_at safe) in TFC.
   rewrite ->(spec_at_at safe) in TFC.
   repeat rewrite -> (spec_at_at safe).
   rewrite /toyfun.
   rewrite spec_at_later.
   
   eapply (safe_safe_noframe1 _). 
   exact TFC. cancel1. autorewrite with push_at. specintros => x1 x2. apply lforallL with x1. 
   autorewrite with push_at. apply lforallL with x2. autorewrite with push_at. cancel2. cancel1. sbazooka. cancel1. sbazooka. sbazooka. 
   rewrite /ConditionIs. rewrite /stateIsAny. rewrite /PRE. rewrite /stateIsAny. sbazooka. 

   apply weakenContext. clear TFC.
   (* popcode *)
   rewrite /PRE/POST.
   superspecapply popaxiom. 
   (* JMP retreg *)
   superspecapply *. 
   (* Usual logic stuff *)
   setoid_rewrite <- spec_later_weaken. 
   rewrite /POST/PRE/stateIsAny. 
   finish_logic_with sbazooka.
Qed.

