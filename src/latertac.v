(*===========================================================================
    Tactics for the specification logic
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.seq.
Require Import x86proved.bitsrep x86proved.spred x86proved.spec.
Require Import x86proved.x86.reg x86proved.x86.flags. (* for EIP *)
Require Import x86proved.safe x86proved.charge.later.
Require Import x86proved.common_tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module LaterTac.

  Inductive term :=
  | t_safe
  | t_impl (S: term) (t: term)
  | t_atemp (t: term) 
  | t_at (t: term) (R: SPred)
  | t_atro (t: term) (R: SPred)
  | t_later (S: term)
  | t_atom (S: spec)
  | t_and (t1 t2: term)
  | t_or (t1 t2: term)
  .

  Require Import x86proved.safe.
  Fixpoint eval t :=
    match t with
    | t_safe => safe
    | t_impl t1 t2 => eval t1 -->> eval t2
    | t_at t R => eval t @ R
    | t_atemp t => eval t @ empSP
    | t_atro t R => eval t <@ R
    | t_later t => @illater spec _ (eval t)       
    | t_atom S1 => S1
    | t_and t1 t2 => eval t1 //\\ eval t2
    | t_or t1 t2 => eval t1 \\// eval t2
    end.

  (* Don't use ~~ in definition as it won't be unfolded later *)
  Fixpoint simplify ispos t : term :=
    match t with
    | t_safe => t_safe
    | t_impl t1 t2 => t_impl (simplify (if ispos then false else true) t1) (simplify ispos t2)
    | t_atemp t => simplify ispos t
    | t_at t R => t_at (simplify ispos t) R
    | t_atro t R => t_atro (simplify ispos t) R
    | t_later t => if ispos then t_later (simplify ispos t) else  (simplify ispos t)
    | t_atom S1 => t_atom S1
    | t_and t1 t2 => t_and (simplify ispos t1) (simplify ispos t2)
    | t_or t1 t2 => t_or (simplify ispos t1) (simplify ispos t2)
    end.

  Lemma evalSimplify t : eval t |-- eval (simplify true t) /\
                         eval (simplify false t) |-- eval t.
  Proof. induction t => //=.   
  + destruct IHt1 as [H1 H2]. destruct IHt2 as [H3 H4]. 
    split. 
    - rewrite <-H2. by rewrite -> H3. 
    - rewrite ->H1. by rewrite <- H4.
  + destruct IHt as [H1 H2].
    split. rewrite spec_at_emp. by rewrite -> H1. rewrite spec_at_emp. by rewrite -> H2.
  + destruct IHt as [H1 H2].
    split. by rewrite -> H1. by rewrite -> H2.
  + destruct IHt as [H1 H2].
    split. by rewrite -> H1. by rewrite -> H2.
  + destruct IHt as [H1 H2].
    split. cancel1. by rewrite <- spec_later_weaken. 
  + destruct IHt1 as [H1 H2]. destruct IHt2 as [H3 H4].
    split. by rewrite -> H1, <- H3. by rewrite -> H2, <- H4.
  + destruct IHt1 as [H1 H2]. destruct IHt2 as [H3 H4].
    split. by rewrite -> H1, <- H3. by rewrite -> H2, <- H4.
  Qed. 

  Ltac quote_term S :=
    match S with
    | safe => constr:(t_safe)
    | ?S1 -->> ?S2 => let t1 := quote_term S1 in let t2 := quote_term S2 in constr:(t_impl t1 t2)
    | ?S1 //\\ ?S2 => let t1 := quote_term S1 in let t2 := quote_term S2 in constr:(t_and t1 t2)
    | ?S1 \\// ?S2 => let t1 := quote_term S1 in let t2 := quote_term S2 in constr:(t_or t1 t2)
    | ?S @ empSP => let t1 := quote_term S in constr:(t_atemp t1)
    | ?S @ ?R => let t := quote_term S in constr:(t_at t R)
    | ?S <@ ?R => let t := quote_term S in constr:(t_atro t R)
    | |> (?S) => let t := quote_term S in constr:(t_later t)
    | ?S => constr:(t_atom S)
    end.

  Lemma do_simplify t1 t2:
    eval (simplify true t1) |-- eval (simplify false t2) ->  eval t1 |-- eval t2.
  Proof. move => H3.
  rewrite -> (proj1 (evalSimplify t1)). by rewrite <- (proj2 (evalSimplify t2)).  Qed. 

  (* If speed is an issue at some point, we could make rquote take two
     environments: one to insert into and one to lookup in. Our decision
     procedures never care about duplicated atoms on either side -- only atoms
     in common between left and right.

     We first try to do unification up to syntax, and try again after we've simpled *)
  Ltac simpllater :=
     match goal with
     | |- ?P |-- ?Q =>
       let t1 := quote_term P in
       let t2 := quote_term Q in
       eapply (@do_simplify t1 t2); cbv [eval simplify]
     | |- _ => fail 1 "Goal is not a spec entailment"
     end.  

End LaterTac.

Ltac simpllater := LaterTac.simpllater.