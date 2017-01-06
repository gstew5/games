Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema dist games.

(** Operational type classes for 'cost' and 'moves'; 
    cf. "Type Classes for Mathematics in Type Theory", 
        Spitters and van der Weegen,
        http://www.eelis.net/research/math-classes/mscs.pdf*)

Class CostClass (cN : nat) (rty : realFieldType) (cT : finType) :=
  cost_fun : 'I_cN -> {ffun 'I_cN -> cT} -> rty.
Notation "'cost'" := (@cost_fun _ _ _) (at level 30).

Class CostAxiomClass cN rty cT `(CostClass cN rty cT) :=
  cost_axiom (i : 'I_cN) (f : {ffun 'I_cN -> cT}) : 0 <= cost i f.

Section costLemmas.
  Context {N rty T} `(CostAxiomClass N rty T).

  Lemma cost_pos i f : 0 <= cost i f.
  Proof. apply: cost_axiom. Qed.
End costLemmas.
  
(*Instance finCloneCostInstance cN rty cT `(H : CostClass cN rty cT) :
  CostClass cN rty [finType of cT] :=
  @cost_fun cN rty [finType of cT] H.*)

Class MovesClass (mN : nat) (mT : finType) :=
  moves_fun : 'I_mN -> rel mT.
Notation "'moves'" := (@moves_fun _ _) (at level 50).

Class game (T : finType) (N : nat) (rty : realFieldType) 
      `(costAxiomClass : CostAxiomClass N rty T)
       (movesClass : MovesClass N T)
  : Type := {}.

