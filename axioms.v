Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import BinNat Nnat.

Require Import dist.

(** Random number generation *)

Section rand.
  Variable bound : N.
  Variable bound_pos : 0 < N.to_nat bound.

  Lemma N0_leq_bound : N.to_nat N0 < N.to_nat bound.
  Proof. by []. Qed.
  
  Axiom rand : dist [finType of 'I_(N.to_nat bound)] [numDomainType of rat].
  Axiom rand_uniform : rand = uniformDist (Ordinal N0_leq_bound).
End rand.






