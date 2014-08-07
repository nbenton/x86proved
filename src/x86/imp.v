Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad Ssreflect.tuple x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.opred x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.macros.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms x86proved.charge.csetoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Section LanguageDefinitions.
  Inductive var := xa | xb | xc.

  Inductive expr :=
    evar (x: var)
  | eliteral (value: DWORD)
  | esubtract (x y: var)
  | elessthan (x y: var).

  Inductive cmd :=
    Cassign (x: var) (e: expr)
  | Cseq (C1 C2: cmd)
  | Cwhile (e: expr) (C: cmd)
  | Cif (e: expr) (C1 C2: cmd).

  Definition varEq x y :=
    match x, y with
    | xa, xa => true
    | xb, xb => true
    | xc, xc => true
    | _ , _ => false
    end.

  Lemma var_eqP: Equality.axiom varEq.
  Proof.
    move=> x y. case: x; case: y; by constructor.
  Qed.

  Canonical var_eqMixin := EqMixin var_eqP.
  Canonical var_eqType := Eval hnf in EqType _ var_eqMixin.

End LanguageDefinitions.

Section Compiler.
  Definition var_reg v : Reg :=
    match v with xa => EAX | xb => EBX | xc => ECX end.

  (* Puts the result in EDX *)
  Definition compile_expr e : program :=
    match e with
    | evar x => MOV EDX, (var_reg x)
    | eliteral v => MOV EDX, v
    | esubtract x1 x2 =>
        let r1 := var_reg x1 in
        let r2 := var_reg x2 in
        MOV EDX, r1;;
        SUB EDX, r2
    | elessthan x1 x2 =>
        if x1 == x2 then
          (* this special case is my coward's way out of proving a general rule
             for CMP. *)
          (MOV EDX, 0): program
        else
          let r1 := var_reg x1 in
          let r2 := var_reg x2 in
          (* The tricky bit is to move the carry flag into a register *)
          CMP r1, r2;;
          MOV EDX, 0;;
          ADC EDX, 0
    end.

  Definition compile_condition (e: expr) : program :=
    compile_expr e;; TEST EDX, EDX.

  Fixpoint compile_cmd (C: cmd) : program :=
    match C with
    | Cassign dst e => compile_expr e;; MOV (var_reg dst), EDX
    | Cseq C1 C2 => prog_seq (compile_cmd C1) (compile_cmd C2)
    | Cwhile e C =>
        while (compile_condition e) CC_Z false (
          compile_cmd C
        )
    | Cif e C1 C2 =>
        compile_condition e;;
        ifthenelse CC_Z false (
          compile_cmd C1
        ) (
          compile_cmd C2
        )
    end.
End Compiler.

Section LogicDefinitions.
  Definition stack := var -> DWORD.

  Instance stackEquiv : Equiv stack := {
     equiv s1 s2 := forall n, s1 n = s2 n
  }.

  Instance stackType : type stack.
  Proof.
    split.
    move => s n; reflexivity.
    move => s1 s2 Hs n; specialize (Hs n); symmetry; assumption.
    move => s1 s2 s3 H12 H23 n; specialize (H12 n); specialize (H23 n).
    transitivity (s2 n); assumption.
  Qed.

  Definition asn := ILFunFrm stack Prop.

  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.

  Global Instance asn_ops : ILogicOps asn := _.
  Global Instance asn_logic : ILogic asn := _.

  Definition mkAsn (P : stack -> Prop) := mkILFunFrm stack Prop P.
  Global Implicit Arguments mkAsn [].

  Definition stack_denot (s: stack) :=
    EAX ~= s xa ** EBX ~= s xb ** ECX ~= s xc.

  Definition asn_denot (P: asn) : SPred :=
    Exists s, P s /\\ stack_denot s.

  (* The high-level triple for the imp language. It lives in the low-level spec
     logic, which is maybe not really appropriate, but it works. *)
  Definition triple (P: asn) (C: cmd) (Q: asn) : spec :=
    loopy_basic (asn_denot P) (compile_cmd C) empOP (asn_denot Q) @ (EDX? ** OSZCP?).

  (* Expression evaluation *)
  Definition eeval (e: expr) (s: stack) : DWORD :=
    match e with
    | evar x => s x
    | eliteral v => v
    | esubtract x1 x2 => subB (s x1) (s x2)
    | elessthan x1 x2 => if ltB (s x1) (s x2) then #1 else #0
    end.

  (* A substitution in its most general form maps variable names to
     expressions. *)
  Definition substitution := var -> expr.

  (* This is the substitution that replaces x with e and leaves all other
     variables unchanged. *)
  Definition subst1 e x : substitution :=
    fun y => if y == x then e else evar y.

  (* Apply a substitution to a stack *)
  Definition stack_subst (f: substitution) (s: stack) : stack :=
    fun x => eeval (f x) s.

  (* Apply a substitution to an assertion or an evaluated expression *)

   Definition subst {A} (f: substitution) (E: stack -> A) : stack -> A :=
    fun s => E (stack_subst f s).

   Require Import Coq.Logic.FunctionalExtensionality.

   Program Definition asn_subst (f : substitution) (E : stack -> Prop) : asn:=
     mkAsn (subst f E) _.
   Next Obligation.
     assert (subst f E t = subst f E t').
     apply f_equal; apply functional_extensionality; apply H.
     rewrite <- H1; assumption.
   Qed.

End LogicDefinitions.

Notation "E [ e // x ]" := (subst (subst1 e x) E)
  (at level 7, left associativity, format "E [ e  //  x ]").

Section LogicLemmas.
  (* It's possible to pull out one stack variable, change it, and then get back
     a state corresponding to a substitution on the original stack. *)
  Lemma var_assign_subst x e s:
    stack_denot s |-- var_reg x ~= s x **
      (var_reg x ~= eeval e s -* stack_denot (stack_subst (subst1 e x) s)).
  Proof.
    rewrite /stack_denot. rewrite /stack_subst /subst1.
    case: x => /=; ssimpl; apply wandSPAdj; by ssimpl.
  Qed.

  (* Read-only version of the above *)
  Lemma regs_read_var x s:
    stack_denot s |-- var_reg x ~= s x **
      (var_reg x ~= s x -* stack_denot s).
  Proof.
    rewrite /stack_denot.
    case: x => /=; ssimpl; apply: wandSPAdj; by ssimpl.
  Qed.

  (* Terrible hack *)
  Lemma regs_read_vars x y s:
    y <> x ->
    stack_denot s |-- var_reg x ~= s x ** var_reg y ~= s y **
                     (var_reg x ~= s x ** var_reg y ~= s y -* stack_denot s).
  Proof.
    rewrite /stack_denot.
    case: x; case: y => //= _; ssimpl; apply wandSPAdj; by ssimpl.
  Qed.

  Lemma sepSPwand P Q:
    P ** (P -* Q) |-- Q.
  Proof. rewrite sepSPC. exact: sepSPAdj. Qed.

  Lemma lt_irreflexive x: (x < x) = false.
  Proof. by elim: x. Qed.

  Lemma leBltB_neg {n} (x y: BITS n): ltB x y = ~~leB y x.
  Proof. by rewrite ltB_nat leB_nat ltnNge. Qed.

  (** TODO(t-jagro): Move this elsewhere *)
  Lemma adcB_b_0_0 b : adcB b #(0) #(0) = (false, @fromNat n32 (if b then 1 else 0)).
  Proof.
    rewrite /adcB adcBmain_nat splitmsb_fromNat toNat_fromNat0. rewrite [X in #(X)]/=. rewrite !addn0.
    rewrite /nat_of_bool.
      by destruct b.
  Qed.

  Lemma compile_expr_correct s e:
    |-- loopy_basic EDX? (compile_expr e) empOP (EDX ~= eeval e s)
        @ (stack_denot s ** OSZCP?).
  Proof.
    autorewrite with push_at.
    case: e; rewrite /compile_expr/eeval/natAsDWORD;
    intros;
    repeat repeat
           lazymatch goal with
             | [ |- ?x |-- ?x ] => reflexivity
             | [ H : (?x == ?y) = _ |- _ ] => move /eqP in H; subst
             | [ H : ltB ?x ?x = true |- _ ] => rewrite ltB_nat lt_irreflexive in H; by inversion H
             | [ |- context[ltB ?x ?x] ] => rewrite (ltB_nat x x) lt_irreflexive
             | [ |- ?P ** (?P -* ?Q) |-- _ ] => rewrite -> sepSPwand
             | [ |- ?P ** ((?P -* ?Q) ** _) |-- _ ] => rewrite <- sepSPA, -> sepSPwand
             | [ |- context[OPred_pred (default_PointedOPred ?x)] ] => change (OPred_pred (default_PointedOPred x)) with x
             | [ |- context[catOP empOP ?x] ] => rewrite -> empOPL
             | [ |- context[catOP ?x empOP] ] => rewrite -> empOPR
             | [ H : context[ltB ?x ?y] |- _ ] => rewrite leBltB_neg in H
             | [ H : is_true (leB ?x ?y), H' : context[leB ?x ?y] |- _ ] => rewrite H in H'; simpl in H'
             | [ H : is_true (~~leB ?x ?y), H' : context[leB ?x ?y] |- _ ] => rewrite H in H'; simpl in H'
             | [ H : false = true |- _ ] => by inversion H
             | [ H : true = false |- _ ] => by inversion H
             | [ |- _ |-- parameterized_basic _ (prog_instr (MOV RegArg _, ArgSrc (RegArg _))) _ _ ] => try_basicapply MOV_RanyR_rule
             | [ |- _ |-- parameterized_basic _ (prog_instr (SUB RegArg _, ArgSrc (RegArg _))) _ _ ] => try_basicapply SUB_RR_rule
             | [ |- _ |-- parameterized_basic _ (prog_instr (CMP RegArg _, ArgSrc (RegArg _))) _ _ ] => try_basicapply CMP_RR_rule
             | [ |- _ |-- parameterized_basic _ (prog_instr (MOV RegArg _, ConstSrc _)) _ _ ]        => try_basicapply MOV_RanyI_rule
             | [ |- _ |-- parameterized_basic _ (prog_instr (ADC RegArg _, ConstSrc _)) _ _ ]        => try_basicapply ADC_RI_rule
             | |- _ |-- basic _ (prog_seq _ _) _ _       => eapply basic_seq
             | |- _ |-- loopy_basic _ (prog_seq _ _) _ _ => eapply loopy_basic_seq
             | [ |- context[if ?E then _ else _] ] => case_eq E; intro
             | _ => match goal with
                      | [ |- stack_denot _ ** _ |-- RegOrFlagDWORD (regToAnyReg (var_reg _)) ~= _ ** _ ] => by rewrite ->regs_read_var; ssimpl
                      | [ |- stack_denot _ |-- RegOrFlagDWORD (regToAnyReg (var_reg _)) ~= _ ** _ ] => by rewrite ->regs_read_var; ssimpl
                      | [ |- _ ** stack_denot _ |-- (RegOrFlagDWORD (regToAnyReg (var_reg _)) ~= _ ** RegOrFlagDWORD (regToAnyReg (var_reg _)) ~= _) ** _ ] => by rewrite ->regs_read_vars; try ssimpl; trivial
                      | _ => progress (rewrite /OSZCP/stateIsAny; sbazooka)
                      | [ |- context[?P -* ?Q] ] => by etransitivity; [ | eapply sepSPwand ]; sbazooka
                      | [ |- adcB ?b #(0) #(0) = _ ] => eexact (adcB_b_0_0 b)
                      | [ |- context[carry_subB ?x ?y] ] => generalize (sbbB_ltB_leB x y); case_eq (carry_subB x y); intros
                    end
      end.
  Qed.

  Lemma compile_condition_correct s e:
    |-- loopy_basic (EDX? ** OSZCP?) (compile_condition e) empOP
              (EDX? ** ZF ~= (eeval e s == zero _) **
               OF? ** SF? ** CF? ** PF?)
          @ (stack_denot s).
  Proof.
    rewrite /compile_condition. autorewrite with push_at.
    apply: loopy_basic_seq; first try done. have He := (@compile_expr_correct s e).
    autorewrite with push_at in He.
    eapply (basic_basic_context (T:=program)); first apply He.
    - done.
    - by ssimpl.
    - done.
    - reflexivity.
    eapply basic_basic; first by apply weaken_parameterized_basic; apply TEST_self_rule.
    - by ssimpl.
    rewrite /stateIsAny /OSZCP. by sbazooka; reflexivity.
  Qed.
End LogicLemmas.

Section LogicRules.
  Theorem triple_assign (Q : asn) e x S:
    S |-- triple (asn_subst (subst1 e x) Q) (Cassign x e) Q.
  Proof.
    rewrite /triple /=. autorewrite with push_at. rewrite {1}/asn_denot.
    specintros => s Hsubst.
    eapply loopy_basic_seq; first done.
    - have He := (@compile_expr_correct s e).
      autorewrite with push_at in He. eapply (basic_basic_context (T:=program)).
      - apply He.
      - done.
      - by ssimpl.
      - done.
      reflexivity.
    - eapply basic_basic; first by apply weaken_parameterized_basic; apply MOV_RanyR_rule.
      - rewrite ->var_assign_subst with (e:=e) (x:=x).
        rewrite /stack_denot. ssimpl. rewrite {6}/stateIsAny. sbazooka.
      rewrite /stateIsAny. sbazooka. rewrite /asn_denot /stack_denot.
      rewrite ->sepSPwand. ssplits; first apply Hsubst. by sbazooka.
  Qed.

  Local Instance asn_denot_entails:
    Proper (lentails ++> lentails) asn_denot.
  Proof.
    move=> P P' HPP'. rewrite /asn_denot.
    sdestructs => s HP. ssplits; last reflexivity.
    specialize (HPP' s HP). assumption.
  Qed.

  Theorem triple_roc P' Q' S P C Q:
    P |-- P' ->
    Q' |-- Q ->
    S |-- triple P' C Q' ->
    S |-- triple P C Q.
  Proof. rewrite /triple. move=> HP HQ HS. by rewrite ->HP, <-HQ. Qed.

  Theorem triple_exists A S f C Q:
    (forall a:A, S |-- triple (f a) C Q) ->
    S |-- triple (lexists f) C Q.
  Proof.
    rewrite /triple. move=> H. rewrite /asn_denot. autorewrite with push_at.
    specintros => s [a Ha]. specialize (H a). autorewrite with push_at in H.
    eapply basic_roc_pre; last apply H.
    rewrite /asn_denot. by sbazooka.
  Qed.

  Theorem triple_seq Q S P R C1 C2:
    S |-- triple P C1 Q ->
    S |-- triple Q C2 R ->
    S |-- triple P (Cseq C1 C2) R.
  Proof.
    rewrite /triple. autorewrite with push_at.
    move=> H1 H2. simpl compile_cmd.
    eapply loopy_basic_seq; first try done. rewrite -/compile_cmd -/interpProgram.
    - apply H1.
    - apply H2.
  Qed.

  Program Definition blurb e b := mkAsn (fun s => (eeval e s == zero _) = b) _.
  Next Obligation.
    assert (eeval e t = eeval e t').
    apply f_equal; apply functional_extensionality; apply H.
    rewrite H0. reflexivity.
  Qed.

  Theorem triple_while S (P : asn) e C:
    S |-- triple (blurb e false //\\ P) C P ->
    S |-- triple P (Cwhile e C) ((blurb e true) //\\ P).
  Proof.
    rewrite /triple. autorewrite with push_at. move=> HC. simpl compile_cmd.
    set (I := fun b:bool =>
      asn_denot ((blurb e b) //\\ P) **
      EDX? ** OF? ** SF? ** CF? ** PF?).
    eapply basic_roc_post; first last; first apply (while_rule (I:=I)).
    - rewrite /asn_denot. specintros => s HP.
      have He := (@compile_condition_correct s e).
      autorewrite with push_at in He.
      eapply (basic_basic_context (T:=program)); first apply He.
      + done.
      + by ssimpl.
      + done.
      rewrite /I /asn_denot /ConditionIs. by sbazooka.
    - eapply basic_roc_pre; last apply HC.
      rewrite /I /ConditionIs /stateIsAny. by sbazooka.
    - rewrite /I /ConditionIs /stateIsAny /negb. by sbazooka.
  Qed.

  Theorem triple_if S P e C1 C2 Q:
    S |-- triple ((blurb e false) //\\ P) C1 Q ->
    S |-- triple ((blurb e true) //\\ P) C2 Q ->
    S |-- triple P (Cif e C1 C2) Q.
  Proof.
    rewrite /triple. autorewrite with push_at. move=> HC1 HC2 /=.
    rewrite [_ P]/asn_denot. specintros => s HP.
    apply: loopy_basic_seq; first done.
    - have He := (@compile_condition_correct s e).
      autorewrite with push_at in He.
      eapply (basic_basic_context (T:=program)); first apply He.
      + done.
      + by ssimpl.
      + done.
      reflexivity.
    set (I := fun b:bool =>
      asn_denot ((blurb e b) //\\ P) **
      EDX? ** OF? ** SF? ** CF? ** PF?).
    apply: basic_roc_pre; last apply (if_loopy_rule (P:=I)).
    - rewrite /I /asn_denot /ConditionIs. by sbazooka.
    - eapply basic_roc_pre; last apply HC1.
      rewrite /I /ConditionIs /stateIsAny. by sbazooka.
    - eapply basic_roc_pre; last apply HC2.
      rewrite /I /ConditionIs /stateIsAny /negb. by sbazooka.
  Qed.

  Local Transparent ILFun_Ops.
  Lemma subst_true_special_case (e : expr) (x: var): |-- (asn_subst (subst1 e x) (ltrue:asn)).
  Proof. move=> s _. apply I. Qed.

End LogicRules.
