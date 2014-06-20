Ltac type_of t := type of t (* ssreflect bug workaround *).
(*===========================================================================
    Rules for x86 instructions in terms of [safe]
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Export x86.instrrules.core.

Require Export x86.instrrules.adc.
Require Export x86.instrrules.addsub.
Require Export x86.instrrules.and.
Require Export x86.instrrules.callrel.
Require Export x86.instrrules.cmp.
Require Export x86.instrrules.incdec.
Require Export x86.instrrules.jccrel.
Require Export x86.instrrules.jmprel.
Require Export x86.instrrules.lea.
Require Export x86.instrrules.mov.
Require Export x86.instrrules.neg.
Require Export x86.instrrules.not.
Require Export x86.instrrules.or.
Require Export x86.instrrules.pop.
Require Export x86.instrrules.push.
Require Export x86.instrrules.ret.
Require Export x86.instrrules.shift.
Require Export x86.instrrules.test.
Require Export x86.instrrules.xor.
