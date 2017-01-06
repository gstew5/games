Set Implicit Arguments.
Unset Strict Implicit.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import games potential smooth.

Local Open Scope ring_scope.

Section CongestionGame.
  Variable T : finType. (** The type of resources *)
  Variable rty : realFieldType.
  Variable num_players : nat. (** The number of players *)

  (** A strategy is a subset of the nodes in [T]: *)
  Definition strategy := {ffun T -> bool}.

  Record affineCostFunction : Type :=
    { aCoeff : rty;
      bCoeff : rty;
      aCoeff_positive : 0 <= aCoeff;
      bCoeff_positive : 0 <= bCoeff
    }.

  Variable costs : {ffun T -> affineCostFunction}.

  Definition evalCost (t : T) (x : nat) : rty :=
    aCoeff (costs t) *+ x + bCoeff (costs t).
  
  Notation st := ((strategy ^ num_players)%type).

  (** The number of users of resource [t] *)
  Definition load (s : st) (t : T) : nat := #|[set i | s i t]|.

  (** The cost to player [i] of outcome [s] *)
  Definition cost (i : 'I_num_players) (s : st) : rty :=
    \sum_t if s i t then evalCost t (load s t) else 0.

  Definition moves (i : 'I_num_players) : rel strategy :=
    [fun _ _ => true].
  
  Definition congestion_gameMixin : gameMixin strategy := Game.Mixin moves cost.
  Canonical CongestionGame := Eval hnf in GameType strategy congestion_gameMixin.

  Lemma Cost_eq (s : (strategy ^ (numplayers CongestionGame))) :
    Cost s = \sum_t (evalCost t (load s t)) *+ load s t.
  Proof.
    rewrite /Cost /= /Game.Exports.cost /Game.cost /= /cost.
    rewrite exchange_big=> /=; apply: congr_big=> // t _.
    by rewrite -big_mkcond /= sumr_const /load /= cardsE.
  Qed.

  Definition rty_of_nat (n : nat) : rty := n%:R.
  
  Lemma christodoulou (y z : nat) :
    (y * (z + 1))%N%:R <= (rty_of_nat 5)/3%:R * y%:R^2 + 1%:R/3%:R * z%:R^2.
  Proof.
  Admitted.

  Lemma christodoulou' (y z : nat) (a b : rty) :
    a * (y * (z + 1))%N%:R + b * y%:R
    <= (rty_of_nat 5)/3%:R * ((a *+ y + b)*+y) + 1%:R/3%:R * ((a *+ z + b)*+z).
  Proof.
  Admitted.

  (*Lemma congestion_smooth_axiom : smooth_axiom ((rty_of_nat 5)/3%:R) (1%:R/3%:R).
  Proof.
    rewrite /smooth_axiom /Game.Exports.cost /Game.cost /= => t t' H.
    have H2: \sum_(i < numplayers CongestionGame)
              cost i [ffun j => if i == j then t' j else t j]
          <= \sum_r (evalCost r (load t r + 1)) *+ load t' r.
    { rewrite /cost exchange_big /=; apply: ler_sum=> r _.
      rewrite -big_mkcond /= /load.
      admit.
    }
    apply: ler_trans; first by apply: H2.
    set x  := load t.
    set x' := load t'.
    rewrite /evalCost.
    have H3:
      forall r,
        (aCoeff (costs r) *+ (x r + 1) + bCoeff (costs r)) *+ x' r
     <= (rty_of_nat 5)/3%:R * ((aCoeff (costs r) *+ (x' r) + bCoeff (costs r))*+(x' r)) +
        1%:R/3%:R * ((aCoeff (costs r) *+ (x r) + bCoeff (costs r))*+(x r)).
    { move=> r; apply: ler_trans; last by apply: christodoulou'.
      admit.
    }
    apply: ler_trans.
    apply: ler_sum.
    { move=> r _.
      apply: (H3 r).
    }
    simpl.
    rewrite big_split /=.
    rewrite 2!Cost_eq /evalCost /x /x'.
    rewrite 2!mulr_sumr.
      by [].
  Admitted.*)
End CongestionGame.
  

    

  
  
