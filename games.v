Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema dist.

Local Open Scope ring_scope.

(** This module defines an interface over multiplayer games. *)

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

  Lemma cost_nonneg i f : 0 <= cost i f.
  Proof. apply: cost_axiom. Qed.
End costLemmas.
  
Class MovesClass (mN : nat) (mT : finType) :=
  moves_fun : 'I_mN -> rel mT.
Notation "'moves'" := (@moves_fun _ _) (at level 50).

Class game (T : finType) (N : nat) (rty : realFieldType) 
      `(costAxiomClass : CostAxiomClass N rty T)
       (movesClass : MovesClass N T)
  : Type := {}.

(***********************)
(** Negative cost game *)

Class NegativeCostAxiomClass cN rty cT `(CostClass cN rty cT) :=
  negative_cost_axiom (i : 'I_cN) (f : {ffun 'I_cN -> cT}) : cost i f <= 0.

Section negativeCostLemmas.
  Context {N rty T} `(NegativeCostAxiomClass N rty T).

  Lemma cost_neg i f : cost i f <= 0.
  Proof. apply: negative_cost_axiom. Qed.
End negativeCostLemmas.

Class negative_cost_game (T : finType) (N : nat) (rty : realFieldType) 
      `(negativeCostAxiomClass : NegativeCostAxiomClass N rty T)
       (movesClass : MovesClass N T)
  : Type := {}.

(** End negative cost game *)
(***************************)

(****************)
(** Payoff game *)

Class PayoffClass (cN : nat) (rty : realFieldType) (cT : finType) :=
  payoff_fun : 'I_cN -> {ffun 'I_cN -> cT} -> rty.
Notation "'payoff'" := (@payoff_fun _ _ _) (at level 30).

Class PayoffAxiomClass cN rty cT `(PayoffClass cN rty cT) :=
  payoff_axiom (i : 'I_cN) (f : {ffun 'I_cN -> cT}) : 0 <= payoff i f.

Section payoffLemmas.
  Context {N rty T} `(PayoffAxiomClass N rty T).

  Lemma payoff_pos i f : 0 <= payoff i f.
  Proof. apply: payoff_axiom. Qed.
End payoffLemmas.

Class payoff_game (T : finType) (N : nat) (rty : realFieldType)
      `(payoffAxiomClass : PayoffAxiomClass N rty T)
       (movesClass : MovesClass N T)
  : Type := {}.

(** End payoff game *)
(********************)

(**************************************)
(** Payoff game -> negative cost game *)

Instance negativeCostInstance_of_payoffInstance
         N rty (T : finType)
         `(payoffInstance : @PayoffClass N rty T)
  : CostClass _ _ _ :=
  fun i f => - payoff i f.

(* 0 <= payoff -> cost <= 0 *)

Instance negativeCostAxiomInstance_of_payoffAxiomInstance
         N rty (T : finType)
         `(payoffAxiomInstance : PayoffAxiomClass N rty T) :
  NegativeCostAxiomClass (negativeCostInstance_of_payoffInstance _).
Proof.
  move=> i f. rewrite /cost_fun /negativeCostInstance_of_payoffInstance.
  rewrite /PayoffAxiomClass in payoffAxiomInstance.
    by rewrite oppr_le0.
Qed.

Instance negative_cost_game_of_payoff_game
         N rty (T : finType)
         `(_ : payoff_game T N rty)
  : negative_cost_game _ _ :=
  Build_negative_cost_game
    (negativeCostAxiomInstance_of_payoffAxiomInstance
       N rty T payoffAxiomClass)
    _. (* payoffAxiomClass is an auto-generated name
          from using the ` thing *)

(******************************************)
(** End payoff game -> negative cost game *)

Local Open Scope ring_scope.

(** An arithmetic fact that should probably be moved elsewhere, and
    also generalized. *)
Lemma ler_mull (rty : realFieldType) (x y z : rty) (Hgt0 : 0 < z) :
  x <= y -> z * x <= z * y.
Proof.
  move=> H; rewrite -ler_pdivr_mull=> //; rewrite mulrA.
  rewrite [z^(-1) * _]mulrC divff=> //; first by rewrite mul1r.
  apply/eqP=> H2; rewrite H2 in Hgt0.
  by move: (ltr0_neq0 Hgt0); move/eqP.
Qed.

(** The iff version of this was causing the apply tactic to hang 
    in the gen_smooth proof for the location residual game. *)
Lemma ler_mull2 (rty : realFieldType) (x y z : rty) (Hgt0 : 0 < z) :
  z * x <= z * y -> x <= y.
Proof.
   move=> H. rewrite -ler_pdivr_mull in H=> //. rewrite mulrA in H.
  rewrite [z^(-1) * _]mulrC divff in H=> //. rewrite mul1r in H.
  apply H. 
  apply/eqP=> H2; rewrite H2 in Hgt0.
  by move: (ltr0_neq0 Hgt0); move/eqP.
Qed.

(** A state is a finite function from player indices to strategies. *)
Definition state N T := ({ffun 'I_N -> T})%type.

Section payoffGameDefs.
  Context {T} {N} `(gameAxiomClassA : payoff_game T N)
          `(gameAxiomClassB : payoff_game T N).
  Definition Payoff (t : state N T) : rty := \sum_i (payoff i t).
End payoffGameDefs.

(** All equilibrium notions are parameterized by a [moves] relation
    (via the typeclass [Moveable T]). *)
Section gameDefs.
  Context {T} {N} `(gameAxiomClassA : game T N) `(gameAxiomClassB : game T N).

  (** We assume there's at least one strategy vector. *)
  Variable t0 : state N T. 
  
  (** Lift a unilateral move to a state update *)
  Definition Move (i : 'I_N) : rel (state N T) :=
    [fun t t' : state N T =>
       [&& moves i (t i) (t' i)
         & [forall j : 'I_N, (i != j) ==> (t j == t' j)]]].
  
  (** [t] is a Pure Nash Equilibrium (PNE) if no player is better off
      by moving to another strategy. *)
  Definition PNE (t : state N T) : Prop :=
    forall (i : 'I_N) (t' : state N T),
      Move i t t' -> cost i t <= cost i t'.

  (** PNE is decidable. *)
  Definition PNEb (t : state N T) : bool :=
    [forall i : 'I_N,
       [forall t' : state N T, Move i t t' ==> (cost i t <= cost i t')]].    

  Lemma PNE_PNEb t : PNE t <-> PNEb t.
  Proof.
    split.
    { move=> H1; apply/forallP=> x //.
      by apply/forallP=> x0; apply/implyP=> H2; apply: H1.
    }
    by move/forallP=> H1 x t' H2; apply: (implyP (forallP (H1 x) t')).
  Qed.

  Lemma PNEP t : reflect (PNE t) (PNEb t).
  Proof.
    move: (PNE_PNEb t).
    case H1: (PNEb t).
    { by move=> H2; constructor; rewrite H2.
    }
    move=> H2; constructor=> H3.
    suff: false by [].
    by rewrite -H2.
  Qed.

  (** The social Cost of a state is the sum of all players' costs. *)
  Definition Cost (t : state N T) : rty := \sum_i (cost i t).

  (** A state is optimal if its social cost can't be improved. *)
  Definition optimal : pred (state N T) :=
    fun t => [forall t0, Cost t <= Cost t0].

  (** The Price of Anarchy for game [T] is the ratio of WORST 
      equilibrium social cost to optimal social cost. We want the 
      ratio to be as close to 1 as possible. *)
  Definition POA : rty :=
    Cost (arg_max PNEb Cost t0) / Cost (arg_min optimal Cost t0).

  (** The Price of Stability for game [T] is the ratio of BEST
      equilibrium social cost to optimal social cost. We want the 
      ratio to be as close to 1 as possible. *)
  Definition POS : rty :=
    Cost (arg_min PNEb Cost t0) / Cost (arg_min optimal Cost t0).

  Lemma POS_le_POA (H1 : PNEb t0) (Hcost : forall t, Cost t > 0) : POS <= POA.
  Proof.
    rewrite /POS /POA.
    move: (min_le_max Cost H1); rewrite /min /max=> H2.
    rewrite ler_pdivr_mulr=> //.
    move: H2; move: (Cost _)=> x; move: (Cost _)=> y.
    have Hx: Cost (arg_min optimal Cost t0) != 0.
    { move: (Hcost (arg_min optimal Cost t0)); rewrite ltr_def.
      by case/andP=> H2 H3. }
    move: Hx; move: (Cost _)=> z Hx H2.
    have H3: (z = z / 1) by rewrite (GRing.divr1 z).
    rewrite {2}H3 mulf_div GRing.mulr1 -GRing.mulrA GRing.divff=> //.
    by rewrite GRing.mulr1.
  Qed.

  (** The expected cost (to player [i]) of a particular distribution
      over configurations.  Note that the distribution [d] need not
      be a product distribution -- in order to define Coarse
      Correlated Equilibria (below), we allow player distributions to
      be correlated with one another. *)
  Definition expectedCost
             (i : 'I_N)
             (d : dist [finType of state N T] rty) :=
    expectedValue d (cost i).

  Definition ExpectedCost (d : dist [finType of state N T] rty) :=
    \sum_(i : 'I_N) expectedCost i d.

  Lemma ExpectedCost_linear d :
    ExpectedCost d
    = expectedValue d (fun v => \sum_(i : 'I_N) (cost i v)).
  Proof.
    rewrite /ExpectedCost /expectedCost /expectedValue.
    by rewrite -exchange_big=> /=; apply/congr_big=> //= i _; rewrite mulr_sumr.
  Qed.

  Definition upd (i : 'I_N) :=
    [fun t t' : (T ^ N)%type =>
       finfun (fun j => if i == j then t' j else t j)].
  
  (** The expected cost of an i-unilateral deviation to strategy [t'] *)
  Definition expectedUnilateralCost
             (i : 'I_N)
             (d : dist [finType of state N T] rty)
             (t' : state N T) :=
    expectedValue d (fun t : state N T => cost i (upd i t t')).

  Lemma expectedUnilateralCost_linear d t' :
    \sum_(i < N) expectedUnilateralCost i d t'
    = expectedValue d (fun t : state N T =>
                         \sum_(i : 'I_N) cost i (upd i t t')).
  Proof.
    rewrite /expectedUnilateralCost /expectedValue.
    by rewrite -exchange_big=> /=; apply/congr_big=> //= i _; rewrite mulr_sumr.
  Qed.

  (** \epsilon-Approximate Coarse Correlated Equilibria
      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state (t' i) is greater
      or equal to (1 + \epsilon) times the expected cost of distribution [d].

      NOTES: 
      - [t'] must be a valid move for [i] from any state in the 
        support of [d].

      - For this definition to make sense in context, the cost function 
        for game [T] should be normalized to range [0,1].
   *)
  Definition eCCE (epsilon : rty) (d : dist [finType of state N T] rty) : Prop :=
    forall (i : 'I_N) (t' : state N T),
      (forall t : state N T, t \in support d -> Move i t (upd i t t')) -> 
      expectedCost i d <= (1 + epsilon) * expectedUnilateralCost i d t'.

  Definition eCCEb (epsilon : rty) (d : dist [finType of state N T] rty) : bool :=
    [forall i : 'I_N,
       [forall t' : state N T,
          [forall t : state N T, (t \in support d) ==> Move i t (upd i t t')]
      ==> (expectedCost i d <= (1 + epsilon) * expectedUnilateralCost i d t')]].

  Lemma eCCE_eCCEb eps d : eCCE eps d <-> eCCEb eps d.
  Proof.
    split.
    { move=> H1; apply/forallP=> x; apply/forallP=> y; apply/implyP=> H2.
      by apply: H1=> // t H3; move: H2; move/forallP/(_ t)/implyP/(_ H3).
    }
    move/forallP=> H1 x y; move: (forallP (H1 x)); move/(_ y)/implyP=> H2.
    by move=> H3; apply: H2; apply/forallP=> x0; apply/implyP=> H4; apply: H3.
  Qed.    
    
  Lemma eCCEP eps d : reflect (eCCE eps d) (eCCEb eps d).
  Proof.
    move: (eCCE_eCCEb eps d); case H1: (eCCEb eps d).
    by move=> H2; constructor; rewrite H2.
    by move=> H2; constructor; rewrite H2.
  Qed.

  (** Coarse Correlated Equilibria
      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state (t' i) is greater
      or equal to the expected cost of distribution [d]. 

      NOTES: 
      - [t'] must be a valid move for [i] from any state in the 
        support of [d].
   *)
  Definition CCE (d : dist [finType of state N T] rty) : Prop := eCCE 0 d.

  Lemma CCE_elim (d : dist [finType of state N T] rty) (H1 : CCE d) :
    forall (i : 'I_N) (t' : state N T),
    (forall t : state N T, t \in support d -> Move i t (upd i t t')) ->
    expectedCost i d <= expectedUnilateralCost i d t'.
  Proof.
    rewrite /CCE /eCCE in H1 => i t' H2.
    by move: (H1 i t' H2); rewrite addr0 mul1r.
  Qed.    

  Definition CCEb (d : dist [finType of state N T] rty) : bool := eCCEb 0 d.

  Lemma CCE_CCEb d : CCE d <-> CCEb d.
  Proof. apply: eCCE_eCCEb. Qed.
    
  Lemma CCEP d : reflect (CCE d) (CCEb d).
  Proof. apply: eCCEP. Qed.
  
  (** Mixed Nash Equilibria
      ~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state (t' i) is greater
      or equal to the expected cost of distribution [d]. 

      NOTES: 
      - [d] must be a product distribution, of the form 
        [d_0 \times d_1 \times ... \times d_{#players-1}].

      - [t'] must be a valid move for [i] from any state in the 
        support of [d].
   *)
  Definition MNE (f : {ffun 'I_N -> dist T rty}) : Prop :=
    CCE (prod_dist f).
  
  Definition MNEb (f : {ffun 'I_N -> dist T rty}) : bool :=
    CCEb (prod_dist f).

  Lemma MNE_MNEb d : MNE d <-> MNEb d.
  Proof. by apply: CCE_CCEb. Qed.
    
  Lemma MNEP d : reflect (MNE d) (MNEb d).
  Proof. by apply: CCEP. Qed.
End gameDefs.
