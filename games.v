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
Lemma ler_mull (rty : realFieldType) (x y z : rty) (Hgt0 : 0 <= z) :
  x <= y -> z * x <= z * y.
Proof.
  move=> H.
  rewrite le0r in Hgt0. move: Hgt0 => /orP [Heq0|Hgt0].
  move: Heq0 => /eqP ->. by rewrite 2!mul0r.
  rewrite -ler_pdivr_mull=> //; rewrite mulrA.
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

  (** We assume there's at least one strategy vector. 
      (In fact, we assume two -- though they may equal one another. 
       This makes it easier to state potentially conflicting assumptions on 
       distinct uses of t0 and t1.*)
  Variable t0 : state N T.
  Variable t1 : state N T.   
  
  Definition upd (i : 'I_N) :=
    [fun t : (T ^ N)%type =>
       [fun t_i' : T => 
          finfun (fun j => if i == j then t_i' else t j)]].
  
  (** [t] is a Pure Nash Equilibrium (PNE) if no player is better off
      by moving to another strategy. *)
  Definition PNE (t : state N T) : Prop :=
    forall (i : 'I_N) (t_i' : T),
      moves i (t i) t_i' -> cost i t <= cost i (upd i t t_i').

  (** PNE is decidable. *)
  Definition PNEb (t : state N T) : bool :=
    [forall i : 'I_N,
      [forall t_i' : T,
        moves i (t i) t_i' ==> (cost i t <= cost i (upd i t t_i'))]].    

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

  Lemma Cost_nonneg t : 0 <= Cost t.
  Proof. by apply: sumr_ge0 => i _; apply: cost_nonneg. Qed.
  
  (** A state is optimal if its social cost can't be improved. *)
  Definition optimal : pred (state N T) :=
    fun t => [forall t0, Cost t <= Cost t0].

  Lemma arg_min_optimal_eq : optimal (arg_min predT Cost t0).
  Proof.
    have Hx: predT t0 by [].
    case: (andP (@arg_minP _ _ predT Cost t0 Hx)) => Hy Hz.
    apply/forallP => t2; apply: (forallP Hz).
  Qed.    

  (** The Price of Anarchy for game [T] is the ratio of WORST 
      equilibrium social cost to optimal social cost. We want the 
      ratio to be as close to 1 as possible. *)
  Definition POA : rty :=
    Cost (arg_max PNEb Cost t0) / Cost (arg_min predT Cost t1).

  (** The Price of Stability for game [T] is the ratio of BEST
      equilibrium social cost to optimal social cost. We want the 
      ratio to be as close to 1 as possible. *)
  Definition POS : rty :=
    Cost (arg_min PNEb Cost t0) / Cost (arg_min predT Cost t1).

  Lemma POS_le_POA (H1 : PNEb t0) : POS <= POA.
  Proof.
    rewrite /POS /POA.
    move: (min_le_max Cost H1); rewrite /min /max=> H2.
    case Hx: (Cost (arg_min predT Cost t1) == 0).
    { by move: (eqP Hx) => ->; rewrite invr0 2!mulr0. }
    rewrite ler_pdivr_mulr=> //.
    move: H2 Hx; move: (Cost _)=> x; move: (Cost _)=> y.
    move: (Cost _)=> z Hx H2.
    have H3: (z = z / 1) by rewrite (GRing.divr1 z).
    rewrite {2}H3 mulf_div GRing.mulr1 -GRing.mulrA GRing.divff=> //.
    by rewrite GRing.mulr1.
    by apply/eqP => H4; rewrite H4 eq_refl in H2.
    move: (Cost_nonneg (arg_min predT Cost t1)); rewrite le0r; move/orP; case => //.
    by move/eqP => Hy; rewrite Hy eq_refl in Hx. 
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
  
  Definition expectedCondCost
             (i : 'I_N)
             (d : dist [finType of state N T] rty)
             (t_i : T) :=
    expectedCondValue
      d
      (fun t : state N T => cost i t)
      [pred tx : state N T | tx i == t_i].
  
  (** The expected cost of an i-unilateral deviation to strategy [t' i] *)
  Definition expectedUnilateralCost
             (i : 'I_N)
             (d : dist [finType of state N T] rty)
             (t_i' : T) :=
    expectedValue d (fun t : state N T => cost i (upd i t t_i')).

  Lemma expectedUnilateralCost_linear d t' :
    \sum_(i < N) expectedUnilateralCost i d (t' i)
    = expectedValue d (fun t : state N T =>
                         \sum_(i : 'I_N) cost i (upd i t (t' i))).
  Proof.
    rewrite /expectedUnilateralCost /expectedValue.
    by rewrite -exchange_big=> /=; apply/congr_big=> //= i _; rewrite mulr_sumr.
  Qed.

  (** The expected cost of an i-unilateral deviation to strategy [t' i], 
      conditioned on current i-strategy equal [t_i]. *)
  Definition expectedUnilateralCondCost
             (i : 'I_N)
             (d : dist [finType of state N T] rty)
             (t_i t_i' : T) :=
    expectedCondValue
      d
      (fun t : state N T => cost i (upd i t t_i'))
      [pred tx : state N T | tx i == t_i].
  
  (** \epsilon-Approximate Correlated Equilibria
      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state (t' i), 
      conditioned on current strategy (t i), is no greater than 
       \epsilon plus the expected cost of distribution [d].

      NOTES: 
      - [t' i] must be a valid move for [i] from [t i].
   *)
  Definition eCE (epsilon : rty) (d : dist [finType of state N T] rty) : Prop :=
    forall (i : 'I_N) (t_i t_i' : T),
      (forall t : state N T, t i = t_i -> t \in support d -> moves i t_i t_i') -> 
      expectedCondCost i d t_i <= expectedUnilateralCondCost i d t_i t_i' + epsilon.

  Definition eCEb (epsilon : rty) (d : dist [finType of state N T] rty) : bool :=
    [forall i : 'I_N,
      [forall t_i : T,
        [forall t_i' : T, 
          [forall t : state N T, (t i == t_i) ==> (t \in support d) ==> moves i t_i t_i']
          ==> (expectedCondCost i d t_i <= expectedUnilateralCondCost i d t_i t_i' + epsilon)]]].

  Lemma eCE_eCEb eps d : eCE eps d <-> eCEb eps d.
  Proof.
    split.
    { move=> H1; apply/forallP=> x; apply/forallP=> y; apply/forallP=> z; apply/implyP=> H2.
      apply: H1=> // t H3; move: H2; move/forallP/(_ t)/implyP => H4 H5.
      by rewrite H3 in H4; move: (H4 (eq_refl y)); move/implyP; apply.
    }
    move/forallP => H1 ix t_i t' H2.
    move: (forallP (H1 ix)); move/(_ t_i)/forallP/(_ t')/implyP; apply.
    apply/forallP => t''; apply/implyP; move/eqP => He; subst t_i.
    by apply/implyP => H4; apply: H2.
  Qed.    
    
  Lemma eCEP eps d : reflect (eCE eps d) (eCEb eps d).
  Proof.
    move: (eCE_eCEb eps d); case H1: (eCEb eps d).
    by move=> H2; constructor; rewrite H2.
    by move=> H2; constructor; rewrite H2.
  Qed.
  
  Definition CE (d : dist [finType of state N T] rty) : Prop := eCE 0 d.

  Definition CEb (d : dist [finType of state N T] rty) : bool := eCEb 0 d.

  Lemma CE_CEb d : CE d <-> CEb d.
  Proof. apply: eCE_eCEb. Qed.
    
  Lemma CEP d : reflect (CE d) (CEb d).
  Proof. apply: eCEP. Qed.
  
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
    CE (prod_dist f).
  
  Definition MNEb (f : {ffun 'I_N -> dist T rty}) : bool :=
    CEb (prod_dist f).

  Lemma MNE_MNEb d : MNE d <-> MNEb d.
  Proof. by apply: CE_CEb. Qed.
    
  Lemma MNEP d : reflect (MNE d) (MNEb d).
  Proof. by apply: CEP. Qed.
  
  (** \epsilon-Approximate Coarse Correlated Equilibria
      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state (t' i) is no greater
       \epsilon plus the expected cost of distribution [d].

      NOTES: 
      - [t' i] must be a valid move for [i] from any state in the 
        support of [d].
   *)
  Definition eCCE (epsilon : rty) (d : dist [finType of state N T] rty) : Prop :=
    forall (i : 'I_N) (t_i' : T),
      (forall t : state N T, t \in support d -> moves i (t i) t_i') -> 
      expectedCost i d <= expectedUnilateralCost i d t_i' + epsilon.

  Lemma ler_psum
     : forall (R : numDomainType) (I : Type) (r : seq I) 
              (P Q : pred I) (F : I -> R),
       (forall i, 0 <= F i) ->  
       (forall i : I, P i -> Q i) ->
       \sum_(i <- r | P i) F i <= \sum_(i <- r | Q i) F i.
  Proof.
    move => R I r P Q F Hpos Hx; elim: r; first by rewrite !big_nil.
    move => a l IH; rewrite !big_cons.
    case Hp: (P a).
    { rewrite (Hx _ Hp); apply: ler_add => //. }
    case Hq: (Q a) => //.
    rewrite -[\sum_(j <- l | P j) F j]addr0 addrC; apply ler_add => //.
  Qed.    
    
  Lemma ler_psum_simpl
     : forall (R : numDomainType) (I : Type) (r : seq I) 
              (P : pred I) (F : I -> R),
       (forall i, 0 <= F i) ->        
       \sum_(i <- r | P i) F i <= \sum_(i <- r) F i.
  Proof.
    move => R I r P F Hpos. 
    have ->: \sum_(i <- r) F i = \sum_(i <- r | predT i) F i.
    { apply: congr_big => //. }
    apply ler_psum => //.
  Qed.

  Definition eCCEb (epsilon : rty) (d : dist [finType of state N T] rty) : bool :=
    [forall i : 'I_N,
       [forall t_i' : T,
          [forall t : state N T, (t \in support d) ==> moves i (t i) t_i']
      ==> (expectedCost i d <= expectedUnilateralCost i d t_i' + epsilon)]].

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

  Lemma marginal_unfold (F : {ffun 'I_N -> T} -> rty) i :
    let P t (p : {ffun 'I_N -> T}) := p i == t in     
    \sum_(p : [finType of (T * {ffun 'I_N -> T})] | P p.1 p.2) (F p.2) =
    \sum_(p : {ffun 'I_N -> T}) (F p).
  Proof.
    move => P.
    set (G (x : T) y := F y).
    have ->:
      \sum_(p | P p.1 p.2) F p.2 =
      \sum_(p | predT p.1 && P p.1 p.2) G p.1 p.2 by apply: eq_big.
    rewrite -pair_big_dep /= /G /P.
    have ->:
         \sum_i0 \sum_(j : {ffun 'I_N -> T} | j i == i0) F j =
    \sum_i0 \sum_(j : {ffun 'I_N -> T} | predT j && (j i == i0)) F j.
    { by apply: eq_big. }
    rewrite -partition_big //. 
  Qed.      
  
  Lemma sum1_sum (f : state N T -> rty) i :
    \sum_(ti : T) \sum_(t : state N T | [pred tx | tx i == ti] t) f t =
    \sum_t f t.
  Proof. by rewrite -(marginal_unfold f i) pair_big_dep //. Qed.
  
  Lemma CE_CCE d : CE d -> CCE d.
  Proof.
    move => Hx i t_i' H2; rewrite /CE in Hx; move: (Hx i).
    rewrite /expectedUnilateralCost /expectedUnilateralCondCost
            /expectedCost /expectedCondCost /expectedValue /expectedCondValue.
    move => Hy.
    rewrite addr0.
    have ->: \sum_t d t * (cost) i t =
             \sum_ti \sum_(t : state N T | [pred tx | tx i == ti] t) d t * (cost) i t.
    { by rewrite -(sum1_sum _ i). }
    have Hz:
      \sum_(ti : T) \sum_(t : state N T | [pred tx | tx i == ti] t) d t * (cost) i t <=
      \sum_(ti : T) (\sum_(t : state N T | [pred tx | tx i == ti] t) d t * (cost) i (upd i t t_i')).
    { apply: ler_sum => tx _ //.
      move: (Hy tx t_i'); rewrite addrC add0r / probOf => Hz; clear Hy.
      have Hw:
        (\sum_(t : state N T | [pred tx0 | tx0 i == tx] t) d t * (cost) i t) /
        (\sum_(t : state N T | [pred tx0 | tx0 i == tx] t) d t) <=
        (\sum_(t : state N T | [pred tx0 | tx0 i == tx] t) d t * (cost) i (((upd i) t) t_i')) /
        (\sum_(t : state N T | [pred tx0 | tx0 i == tx] t) d t).
      { apply: Hz => t <-; apply: H2. } clear Hz H2.
      move: Hw; move: [pred tx0 | _] => p.
      (*TODO: clean up and refactor this proof! *)
      case Heq: (\sum_(t : state N T | p t) d t == 0).
      { move: (eqP Heq) => Heq'.
        have: \sum_(t : state N T | p t) d t * (cost) i t = 0.
        { set (F t := d t * (cost) i t).
          have ->: \sum_(t : state N T | p t) d t * (cost) i t
                 = \sum_(t : state N T| p t) (F t).
          { apply: congr_big => //. }
          apply/eqP; rewrite psumr_eq0; last first.
          { move => ix; rewrite /F => _; apply: mulr_ge0; first by apply: dist_positive.
            apply: costAxiomClass. }
          apply/allP => t Hin; apply/implyP => Hp; apply/eqP; rewrite /F.
          rewrite psumr_eq0 in Heq => //=; last first.
          { move => ix _; apply: dist_positive. }
          by move: (allP Heq); move/(_ t)/(_ Hin)/implyP/(_ Hp)/eqP => ->; rewrite mul0r. }
        have: \sum_(t : state N T | p t) d t * (cost) i (((upd i) t) t_i') = 0.
        { set (F t := d t * (cost) i (((upd i) t) t_i')).
          have ->: \sum_(t : state N T | p t) d t * (cost) i (((upd i) t) t_i')
                 = \sum_(t : state N T| p t) (F t).
          { apply: congr_big => //. }
          apply/eqP; rewrite psumr_eq0; last first.
          { move => ix; rewrite /F => _; apply: mulr_ge0; first by apply: dist_positive.
            apply: costAxiomClass. }
          apply/allP => t Hin; apply/implyP => Hp; apply/eqP; rewrite /F.
          rewrite psumr_eq0 in Heq => //=; last first.
          { move => ix _; apply: dist_positive. }
          by move: (allP Heq); move/(_ t)/(_ Hin)/implyP/(_ Hp)/eqP => ->; rewrite mul0r. }
        move => -> -> //. }
      (* \sum_(t | p t) d t > 0 *)
      have Hgt: \sum_(t : state N T | p t) d t > 0.
      { rewrite ltr_def; apply/andP; rewrite Heq; split => //.
        apply: sumr_ge0 => ix _; apply: dist_positive. }
      move: Hgt.
      move: (\sum_(t : state N T | _) d t * _) => x.
      move: (\sum_(t : state N T | _) d t * _) => y.      
      move: (\sum_(t : state N T | _) d t) => r.
      rewrite mulrC [_ / _]mulrC => H3.
      by apply: ler_mull2; rewrite invr_gte0. }
    apply: ler_trans.
    { apply: Hz; move => t <- Hs; apply: H2. }
    have ->:
      \sum_t d t * (cost) i (((upd i) t) t_i') =
      \sum_ti \sum_(t : state N T | [pred tx | tx i == ti] t)
         d t * (cost) i (((upd i) t) t_i').
    { by rewrite -(sum1_sum _ i). }    
    by [].
  Qed.
  
  Lemma CCE_elim (d : dist [finType of state N T] rty) (H1 : CCE d) :
    forall (i : 'I_N) (t_i' : T),
    (forall t : state N T, t \in support d -> moves i (t i) t_i') ->
    expectedCost i d <= expectedUnilateralCost i d t_i'.
  Proof.
    rewrite /CCE /eCCE in H1 => i t' H2.
    by move: (H1 i t' H2); rewrite addr0.
  Qed.    

  Definition CCEb (d : dist [finType of state N T] rty) : bool := eCCEb 0 d.

  Lemma CCE_CCEb d : CCE d <-> CCEb d.
  Proof. apply: eCCE_eCCEb. Qed.
    
  Lemma CCEP d : reflect (CCE d) (CCEb d).
  Proof. apply: eCCEP. Qed.
End gameDefs.
