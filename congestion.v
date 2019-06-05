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

  Instance gameInstance : game costAxiomInstance movesInstance := {}.

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
    b * y%:Q <= 5%:Q/3%:Q * (b * y%:Q) + 1%:Q/3%:Q * (b * z%:Q).
  Proof.
    move=> H.
    have ->: (5%:Q / 3%:Q * (b * y%:Q) + 1%:Q / 3%:Q * (b * z%:Q) =
              b * (5%:Q/3%:Q * y%:Q + 1%:Q/3%:Q * z%:Q)).
    { rewrite [b*z%:~R]mulrC.
      rewrite mulrA. rewrite [1%:~R/3%:~R*(z%:~R*b)]mulrA.
      rewrite -mulrA mulrC mulrA.
      rewrite -[1%:~R/3%:~R*z%:R*b]mulrA [z%:R*b]mulrC.
      rewrite [1%:~R/3%:~R*_]mulrC -[b * y%:R * 5%:~R / 3%:~R]mulrA.
      rewrite -[b * y%:R * _]mulrA -[b * z%:R * _]mulrA -mulrDr.
      have H0: (forall a b c, b = c -> a * b = a * c).
      { by move=> t a b' c ->. }
      apply H0. by rewrite mulrC [z%:R * _]mulrC. } 
    rewrite ler_mull => //.
    rewrite -[y%:~R]addr0. apply ler_add. rewrite addr0.
    apply ler_pemull => //.
    apply ler0n. apply mulr_ge0 => //. apply ler0n.
  Qed.

  (* Not sure if this exists somewhere. If not, maybe it should be moved
     somewhere since it's somewhat general *)
  Lemma christodoulou'_l2 (a b c d : rat) :
    a + b + c + d = (a + c) + (b + d).
  Proof. by rewrite -3!addrA [c + (b + d)]addrC -addrA [d + c]addrC. Qed.

  Lemma christodoulou' (y z : nat) (a b : rat) :
    0 <= a -> 0 <= b ->
    a * (y%:Q * (z%:Q + 1)) + b * y%:Q
    <= 5%:Q/3%:Q * ((a *+ y + b)*+y) + 1%:Q/3%:Q * ((a *+ z + b)*+z).
  Proof.
    move=> Ha Hb.
    have ->: ((a *+ y + b) *+ y = a * y%:Q^2 + b * y%:Q).
    { (* weird how this works (mulrC to unfold the square) *)
      by rewrite [_^2]mulrC -mulr_natr -[a*+_]mulr_natr mulrDl mulrA.
    (* by rewrite -mulr_natr -[a *+ y]mulr_natr mulrDl exprSz expr1z mulrA. *) }
    have ->: ((a *+ z + b) *+ z = a * z%:Q^2 + b * z%:Q).
    { by rewrite -mulr_natr -[a *+ z]mulr_natr mulrDl exprSz expr1z mulrA. }
    rewrite mulrDr. rewrite mulrDr. rewrite addrA.
    (* Ugly but fast *)
    rewrite [5%:~R/3%:~R*(a*y%:~R^2)+5%:~R/3%:~R*(b*y%:~R)+
             1%:~R/3%:~R*(a*z%:~R^2)+1%:~R/3%:~R*(b*z%:~R)]christodoulou'_l2.
    apply: ler_add.
    { rewrite 2![a*_^2]mulrC  [_*(y%:~R^2*a)]mulrA  [_*(z%:~R^2*a)]mulrA.
      rewrite [_*y%:~R^2*a]mulrC [_*z%:~R^2*a]mulrC -mulrDr.
      by apply ler_mull, christodoulou. }
    by apply: christodoulou'_l1.
  Qed.

  Instance resourceLambdaInstance 
    : @LambdaClass [finType of strategy] rat_realFieldType| 0 := 5%:Q/3%:Q.

  Program Instance resourceLambdaAxiomInstance
    : @LambdaAxiomClass [finType of strategy] rat_realFieldType _.

  Instance resourceMuInstance
    : MuClass [finType of strategy] rat_realFieldType | 0 := 1%:Q/3%:Q.
  
  Instance resourceMuAxiomInstance
    : @MuAxiomClass [finType of strategy] rat_realFieldType _.
  Proof. by []. Qed.

  Lemma sum_one_term i (t t' : strategy ^ num_players) (r : T) :
    (\sum_(x < num_players)
      (if ((if i == x then t' x else t x) r)
            && (x == i) then 1 else 0))%N =
    (if (t' i) r then 1 else 0)%N.
  Proof. by rewrite -big_mkcond big_mkcondl big_pred1_eq eq_refl. Qed.

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
      have H1: (\sum_(i < num_players |
                      [ffun j => if i == j then t' j else t j] i r)
                 evalCost r
                 #|[set i0 | [ffun j => if i == j then t' j else t j] i0 r]|
                <=
                \sum_(i < num_players |
                      [ffun j => if i == j then t' j else t j] i r)
                 evalCost r (#|[set i0 | t i0 r]| + 1)).
      { apply: ler_sum => i H. apply ler_add. rewrite -mulr_natr. 
        rewrite -[aCoeff (costs r) *+ (#|[set i0 | (t i0) r]| + 1)]mulr_natr.
        apply ler_mull. apply aCoeff_positive.
        rewrite -2!sum1dep_card /= natrD.
        { 
          have ->: ((\sum_(x < num_players |
                           [ffun j => if i == j then t' j else t j] x r) 1)%N
                    = ((\sum_(x < num_players |
                              ([ffun j => if i == j then t' j else t j] x r)
                                && (x == i)) 1)%N +
                       (\sum_(x < num_players |
                              ([ffun j => if i == j then t' j else t j] x r)
                                && (x != i)) 1)%N)%N).
          { by rewrite -bigID. }
          rewrite natrD addrC. apply: ler_add.
          have ->: ((\sum_(x < num_players |
                           ([ffun j => if i == j then t' j else t j] x r)
                             && (x != i)) 1)%N =
                    (\sum_(x < num_players)
                      if ((if i == x then t' x else t x) r)
                           && (x != i) then 1 else 0)%N).
          { rewrite big_mkcond /=.
            by apply congr_big => //; move => i0 _; rewrite ffunE. }
          have ->: ((\sum_(x < num_players | t x r) 1)%N =
                    (\sum_(x < num_players) if t x r then 1 else 0)%N).
          { by rewrite big_mkcond. }
          rewrite ler_nat. apply leq_sum. move => i0 _.
          case i_i0: (i == i0).
          - have ->: ((i0 != i) = false).
            { by rewrite eq_sym; apply /negPf; rewrite i_i0. }
      rewrite andbF.
      case: (t i0 r) => //.
      { have ->: ((i0 != i) = true).
        { rewrite eq_sym. apply (introT (P := i != i0)). apply: idP.
          apply (contraFneq (b := false)). move => H'. rewrite -i_i0  H'.
          apply: eq_refl => //. by []. }
        rewrite andbT => //. } 
        have ->: ((\sum_(x < num_players |
                         ([ffun j => if i == j then t' j else t j] x r)
                           && (x == i)) 1)%N =
                  (\sum_(x < num_players)
                    if (((if i == x then t' x else t x) r)
                          && (x == i)) then 1 else 0)%N).
        { rewrite big_mkcond.
          by apply: congr_big => //;move => i0 _;rewrite ffunE. }
        rewrite sum_one_term. case: (t' i r)  => //. }
        apply lerr. }
      apply: ler_trans; first by apply H1.
      move {H1}.
      have ->: (\sum_(i < num_players |
                      [ffun j => if i == j then t' j else t j] i r)
                 evalCost r (#|[set i0 | (t i0) r]| + 1) =
                \sum_(i < num_players |
                      [ffun j => if i == j then t' j else t j] i r)
                 1 * evalCost r (#|[set i0 | (t i0) r]| + 1)).
      { by apply: congr_big=> // i _; rewrite mul1r. }
      rewrite -mulr_suml -mulr_natr mulrC.
      apply ler_mull. apply evalCost_ge0.
      have ->: (\sum_(i | [ffun j => if i == j then t' j else t j] i r) 1 =
                (\sum_(i |
                       [ffun j => if i == j then t' j else t j] i r) 1)%N%:R).
      { by move => t0; rewrite natr_sum. }
      rewrite sum1_card /=.      
      have ->: (#|[pred i | [ffun j => if i == j then t' j else t j] i r]|
                = #|[pred i | t' i r]|).
      { by apply eq_card => x; rewrite /in_mem /= ffunE eq_refl. }
      have ->: (#|[pred i | (t' i) r]| = #|[set i | (t' i) r]|).
      { apply eq_card => x. rewrite in_set. rewrite /in_mem //. }
      by apply lerr.
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
    { move=> r; apply: ler_trans; last first.
      apply christodoulou'. apply aCoeff_positive. by apply bCoeff_positive.
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
Qed.

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
      _ _ _ _ _ _ _ _ _
  := {}.
End CongestionGame.
