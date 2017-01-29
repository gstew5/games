Set Implicit Arguments.
Unset Strict Implicit.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import games smooth christodoulou.

Local Open Scope ring_scope.

Section CongestionGame.
  Variable T : finType. (** The type of resources *)
  Variable num_players : nat. (** The number of players *)

  (** A strategy is a subset of the nodes in [T]: *)
  Definition strategy := {ffun T -> bool}.

  Record affineCostFunction : Type :=
    { aCoeff : rat;
      bCoeff : rat;
      aCoeff_positive : 0 <= aCoeff;
      bCoeff_positive : 0 <= bCoeff
    }.

  Variable costs : {ffun T -> affineCostFunction}.

  Definition evalCost (t : T) (x : nat) : rat :=
    aCoeff (costs t) *+ x + bCoeff (costs t).

  Lemma evalCost_ge0 t x : 0 <= evalCost t x.
  Proof.
    rewrite /evalCost; apply: addr_ge0.
    { apply: mulrn_wge0.
      apply: aCoeff_positive. }
    apply: bCoeff_positive.
  Qed.
  
  Notation st := ({ffun 'I_num_players -> strategy})%type.

  (** The number of users of resource [t] *)
  Definition load (s : st) (t : T) : nat := #|[set i | s i t]|.

  (** The cost to player [i] of outcome [s] *)
  Definition costFun (i : 'I_num_players) (s : st) : rat :=
    \sum_t if s i t then evalCost t (load s t) else 0.

  Instance costInstance
    : CostClass num_players rat_realFieldType [finType of strategy]
    := costFun.

  Program Instance costAxiomInstance
    : CostAxiomClass costInstance.
  Next Obligation.
    rewrite /(cost) /costInstance /costFun.
    apply big_ind => //; first by apply: addr_ge0.
    move => i0 _; case: ((f i) i0) => //.
    apply: evalCost_ge0.
  Qed.

  Definition movesFun (i : 'I_num_players) : rel strategy :=
    [fun _ _ : strategy => true].

  Instance movesInstance
    : MovesClass num_players [finType of strategy]
    := movesFun.

  Instance gameInstance : game costAxiomInstance movesInstance.

  Lemma Cost_eq (s : (strategy ^ num_players)) :
    Cost s = \sum_t (evalCost t (load s t)) *+ load s t.
  Proof.
    rewrite /Cost /= /(cost) /costInstance /=.
    rewrite exchange_big=> /=; apply: congr_big=> // t _.
    by rewrite -big_mkcond /= sumr_const /load /= cardsE.
  Qed.
  
  Lemma christodoulou (y z : nat) :
    y%:Q * (z%:Q + 1) <= 5%:Q/3%:Q * y%:Q^2 + 1%:Q/3%:Q * z%:Q^2.
  Proof. by apply: Christodoulou.result. Qed.

  Lemma christodoulou'_l1 (y z : nat) (b : rat) :
    0 <= b ->
    b *+ y <= 5%:Q/3%:Q * b *+ y + 1%:Q/3%:Q * b *+ z.
  Proof.
    move=> H.
    have ->: (5%:Q / 3%:Q * b *+ y + 1%:Q / 3%:Q * b *+ z =
              b * (5%:Q / 3%:Q * y%:Q + 1%:Q / 3%:Q * z%:Q)).
    { rewrite -mulr_natr -mulrnAl -[1%:~R/3%:~R *+ _]mulr_natr.
      rewrite -mulrA mulrC mulrA.
      rewrite -[1%:~R/3%:~R*z%:R*b]mulrA [z%:R*b]mulrC.
      rewrite [1%:~R/3%:~R*_]mulrC -[b * y%:R * 5%:~R / 3%:~R]mulrA.
      rewrite -[b * y%:R * _]mulrA -[b * z%:R * _]mulrA -mulrDr.
      admit. (* almost done *)
    }
    rewrite -[b *+ _]mulr_natr ler_mull => //.
    rewrite -[y%:R]addr0. apply ler_add. apply ler_pemull => //.
    apply ler0n. apply mulr_ge0 => //. apply ler0n.
  Admitted.

  Lemma christodoulou' (y z : nat) (a b : rat) :
    0 <= b ->
    a * (y%:Q * (z%:Q + 1)) + b * y%:Q
    <= 5%:Q/3%:Q * ((a *+ y + b)*+y) + 1%:Q/3%:Q * ((a *+ z + b)*+z).
  Proof.
  Admitted. (*TODO*)

  Instance resourceLambdaInstance 
    : @LambdaClass [finType of strategy] rat_realFieldType| 0 := 5%:Q/3%:Q.

  Program Instance resourceLambdaAxiomInstance
    : @LambdaAxiomClass [finType of strategy] rat_realFieldType _.

  Instance resourceMuInstance
    : MuClass [finType of strategy] rat_realFieldType | 0 := 1%:Q/3%:Q.
  
  Instance resourceMuAxiomInstance
    : @MuAxiomClass [finType of strategy] rat_realFieldType _.
  Proof. by []. Qed.

  Lemma resourceSmoothnessAxiom (t t' : (strategy ^ num_players)%type) :
    \sum_(i : 'I_num_players) cost i (upd i t (t' i)) <=
    lambda of [finType of strategy] * Cost t' +
    mu of [finType of strategy] * Cost t.
  Proof.
    rewrite /Cost /(cost) /costInstance /= /costFun.
    rewrite /lambda_val /resourceLambdaInstance.
    rewrite /mu_val /resourceMuInstance.
    have H2: \sum_(i < num_players)
              cost i [ffun j => if i == j then t' j else t j]
          <= \sum_r (evalCost r (load t r + 1)) *+ load t' r.
    { rewrite exchange_big /=; apply: ler_sum=> r _.
      rewrite -big_mkcond /= /load.
      admit. (*TODO*)
    }
    apply: ler_trans.
    { have <-:
      \sum_(i < num_players)
      \sum_t0
         (if [ffun j => if i == j then t' j else t j] i t0
          then
           evalCost t0
             (load [ffun j => if i == j then t' j else t j] t0)
          else 0) =
      \sum_(i < num_players)
      \sum_t0
         (if [ffun j => if i == j then t' i else t j] i t0
          then
           evalCost t0 (load [ffun j => if i == j then t' i else t j] t0)
          else 0).
      apply: congr_big => //.
      move => i _.
      apply: congr_big => // i0 _.
      rewrite !ffunE eq_refl.
      case: ((t' i) i0) => //.
      f_equal.
      f_equal.
      apply/ffunP => e; rewrite !ffunE.
      case He: (i == e) => //.
      { by move: (eqP He) => ->. }
      apply: H2. }
    move {H2}.
    set x  := load t.
    set x' := load t'.
    have H3:
      forall r,
        (aCoeff (costs r) *+ (x r + 1) + bCoeff (costs r)) *+ x' r
     <= 5%:Q/3%:Q * ((aCoeff (costs r) *+ (x' r) + bCoeff (costs r))*+(x' r)) +
        1%:Q/3%:Q * ((aCoeff (costs r) *+ (x r) + bCoeff (costs r))*+(x r)).
    { move=> r; apply: ler_trans;
              last by apply: christodoulou'; apply bCoeff_positive.
      rewrite mulrnDl; apply: ler_add.
      { rewrite -mulrnA.
        move: (aCoeff_positive (costs r)).
        move: (aCoeff _) => c.
        rewrite (le0r c); case/orP.
        { move/eqP => ->; rewrite !mul0r -mulr_natl mulr0 //. }
        move => Hgt.
        have Hge: (0 <= c).
        { rewrite le0r. apply /orP. by right. }
        rewrite -mulr_natl mulrC; apply: ler_mull => //.
        rewrite mulrDr mulr1 mulnDl mul1n.
        rewrite mulrC -intrM -intrD //. }
      by rewrite -mulr_natl mulrC.
    }
    apply: ler_trans.
    apply: ler_sum.
    { move=> r _.
      apply: (H3 r).
    }
    simpl.
    rewrite big_split /= /x /x'.
    rewrite -2!mulr_sumr.
    by rewrite -2!Cost_eq.
  Admitted. (*TODO*)

  Program Instance congestionSmoothAxiomInstance
    : @SmoothnessAxiomClass
        [finType of strategy]
        num_players
        rat_realFieldType
        _ _ _ _ _ _ _ _.
  Next Obligation. by apply: resourceSmoothnessAxiom. Qed.

  Instance congestionSmoothInstance
    : @smooth
        [finType of strategy]
        num_players
        rat_realFieldType
        _ _ _ _ _ _ _ _ _.
End CongestionGame.
