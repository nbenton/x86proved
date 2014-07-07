Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.finfun Ssreflect.fintype Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.tuple.

(* ATBR *)
Require Import ATBR.DecideKleeneAlgebra.
Require Import ATBR.DKA_Definitions.

(* BinPos *)
Require Import BinNums BinPos.


Require Import bitsrep bitsops.

Require Import interfaceATBR.

Definition rO := RegExp.zero.
Definition rE := RegExp.one.
Notation "x !! y" := (RegExp.plus x y) (at level 15, right associativity) : regex_scope.
Notation "x ' y" := (RegExp.dot x y) (at level 55, right associativity): regex_scope.
Notation "x '*'" := (RegExp.star x) (at level 0): regex_scope.
Notation "` c" := (RegExp.var (Pos.of_nat c)) (at level 2): regex_scope.

Local Open Scope regex_scope.

Definition char (c: Ascii.ascii): regex :=
  RegExp.var (Pos.of_nat (Ascii.nat_of_ascii c)).
Notation "'$' c" := (char c)
  ( at level 0) : regex_scope.

Definition any (l: seq regex): regex :=
  foldr (RegExp.plus) rO l.

Notation "'[[' c1 , c2 , .. , cn ']]'" :=
  ((any (map (fun (c: Ascii.ascii) => char c) (c1 :: c2 :: .. [:: cn] ..))))
  (at level 60) : regex_scope.

Notation "'[{' x ',' y '}]'" :=
  (any [seq RegExp.var (Pos.of_nat c) | c <- iota (Ascii.nat_of_ascii x) ((Ascii.nat_of_ascii y) + 1 - (Ascii.nat_of_ascii x))])
  (right associativity, at level 60) : regex_scope.



Definition maybe (r: regex): regex := r !! rE.
Notation "r ?" := (maybe r)
  (at level 2) : regex_scope.

Definition some (r: regex): regex := r ' r *.
Notation "r '+'" := (some r)
  (at level 0) : regex_scope.

Notation "'m/' r '/g'" := r
  (at level 60) : regex_scope.


Delimit Scope regex_scope with regex.


Local Close Scope regex_scope.
