Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Theory.
Require Import QArith.

Require Import games.
Require Import smooth.

Local Open Scope ring_scope.

Module ResourceResidualGame.
  Section resourceResidualGame.
    Variable rty : realFieldType.
    Variable N : nat.

    Definition cost (i : 'I_N) (s : bool ^ N) : rty :=
      if s i then ((N - 2)%:R) else 0.

    Definition Cost (s : bool ^ N) : rty := \sum_(i : 'I_N) (cost i s).

    Definition moves (i : 'I_N) : rel bool := [fun x y => true].
    
    Definition mixin := @Game.Mixin bool N rty moves cost.
    Definition t := GameType bool mixin.

    Definition mixed_cost (i : 'I_N) :=
      [fun t t' : bool ^ N =>
        finfun (fun j => if i == j then t' j else t j)].

    Definition lambda : rty := 1.
    Definition mu : rty := 0.

    Lemma mixed_cost_eq : forall s s',
      \sum_(i : 'I_N) cost i (mixed_cost i s s') = Cost s'.
    Proof.
      move => s s'. rewrite /Cost /=. apply congr_big => //.
      move => i H. rewrite /cost. rewrite ffunE. rewrite eq_refl => //.
    Qed.

    Lemma gen_smooth :
      forall (s s' : bool ^ N),
        \sum_(i : 'I_N) cost i (mixed_cost i s s') <=
        lambda * (Cost s') + mu * (Cost s).
    Proof.
      rewrite /smooth => s s'. rewrite mixed_cost_eq => //.
      rewrite mul0r. rewrite mul1r. rewrite addr0 => //.
    Qed.
  End resourceResidualGame.
End ResourceResidualGame.

Module SmoothResourceResidualGame.
  Section smoothResourceResidualGame.
    Variable rty : realFieldType.
    Variable N : nat.
    Definition g := (ResourceResidualGame.t rty N).
    Definition lambda : rty := 1.
    Definition mu : rty := 0.

    Lemma smoothness : @smooth_axiom g lambda mu.
      rewrite/smooth_axiom. move => t t' _.
      exact (ResourceResidualGame.gen_smooth rty t t').
    Qed.
  
    Instance t : @smooth g := mkSmooth smoothness.
  End smoothResourceResidualGame.
End SmoothResourceResidualGame.

(**********************************************************************)

Module LocationResidualGame.
  Section locationResidualGame.
    Local Open Scope rat_scope.
    
    Variable N : nat.
    Hypothesis le_2_N : 2%:Q <= N%:Q.

    Definition rat_of_bool b : rat := if b then 1 else 0.

    Definition rat_min (a b : rat) : rat :=
      if a <= b then a else b.

    Definition num_players_true (s : bool ^ N) : rat :=
      \sum_(i : 'I_N) (rat_of_bool (s i)).
    Definition num_players_false (s : bool ^ N) : rat :=
      \sum_(i : 'I_N) (1 - rat_of_bool (s i)).

    Definition cost_aux (i : 'I_N) (s : bool ^ N) :=
      \sum_(j : 'I_N) (if i == j then 0 else 1%:Q - (rat_of_bool (s i))).

    Definition cost (i : 'I_N) (s : bool ^ N) : rat :=
      rat_of_bool (s i) * (N%:Q - 2%:Q) +
      (1 - (rat_of_bool (s i))) * rat_min (N%:Q-2%:Q) (cost_aux i s).

    Definition Cost (s : bool ^ N) : rat :=
        \sum_(i : 'I_N) (cost i s).

    Definition Cost'_aux (p : rat) : rat :=
      (p * (p-1%:Q) + (N%:Q-p) * (N%:Q-2%:Q)).

    Definition Cost' (s : bool ^ N) : rat :=
      let p := num_players_false s in
      if p == N%:Q then
        N%:Q * (N%:Q - 2%:Q)
      else
        Cost'_aux p.

    Definition moves (i : 'I_N) : rel bool := [fun x y => true].
    (* Definition mixin := @Game.Mixin bool N rty moves cost. *)
    (* Definition t := GameType bool mixin. *)

    Definition mixed_cost (i : 'I_N) :=
      [fun t t' : bool ^ N =>
         finfun (fun j => if i == j then t' j else t j)].

    Definition lambda : rat := (3%:Q/2%:Q).
    Definition mu : rat := 0%:Q.

    (** The maximum possible Cost (even with entangled costs) *)
    Definition max_Cost : rat := (N%:Q * (N%:Q - 2%:Q)).

    (** Prove Cost' = Cost *)

    Lemma cost_aux_equiv : forall (i : 'I_N) (s : bool ^ N),
      cost_aux i s = num_players_false s - (1 - rat_of_bool (s i)).
    Admitted.

    Lemma rat_min_l : forall a b,
      a <= b ->
      rat_min a b = a.
    Admitted.

    Lemma rat_min_r : forall a b,
        b <= a ->
        rat_min a b = b.
    Admitted.

    Lemma Cev2 : forall i s,
      (num_players_false s == N%:~R)%B = false ->
      cost_aux i s <= N%:Q - 2%:Q.
    Admitted.

    Lemma Cev3 : forall (s : bool ^ N),
      (num_players_false s == N%:Q)%B ->
      Cost s = N%:Q * (N%:Q - 2%:Q).
    Proof.
      move => s H. rewrite /Cost /cost.
    Admitted.
    
    Lemma Cev4 : forall (s : bool ^ N),
      \sum_(i < N)
       (rat_of_bool (s i) * (N%:~R - 2%:~R) +
        (1 - rat_of_bool (s i)) * cost_aux i s) =
      \sum_(i < N)
       (rat_of_bool (s i) * (N%:~R - 2%:~R)) +
      \sum_(i < N) ((1 - rat_of_bool (s i)) * cost_aux i s).
    Admitted.

    Lemma Cev5 : forall (s : bool ^ N),
      \sum_(i < N) rat_of_bool (s i) * (N%:Q - 2%:Q) =
      (N%:Q - num_players_false s) * (N%:Q - 2%:Q).
    Admitted.

    Lemma Cev6 : forall (s : bool ^ N),
      \sum_(i < N) (1 - rat_of_bool (s i)) * cost_aux i s =
      (num_players_false s) * (num_players_false s - 1).
    Admitted.

    Lemma Cost_equiv : forall (s : bool ^ N),
      Cost s = Cost' s.
    Proof.
      move => s. rewrite /Cost'.
      destruct (num_players_false s == N%:Q)%B eqn:H.
      { apply Cev3. apply H. }
      { rewrite /Cost /cost.
        assert (\sum_(i < N)
                 (rat_of_bool (s i) * (N%:~R - 2%:~R) +
                  (1 - rat_of_bool (s i)) * rat_min (N%:~R - 2%:~R) (cost_aux i s)) =
                \sum_(i < N)
                 (rat_of_bool (s i) * (N%:~R - 2%:~R) +
                  (1 - rat_of_bool (s i)) * cost_aux i s)).
        { apply congr_big => //. move => i _. rewrite rat_min_r => //.
          apply Cev2. apply H.
        }
        rewrite H0.
        rewrite Cev4 Cev5 Cev6 addqC /Cost'_aux => //.
      }
    Qed.

    (** Prove the max value wrt any state *)
    Lemma Cost_max : forall s,
      \sum_(i : 'I_N) (cost i s) <= max_Cost /\ exists s', Cost s' = max_Cost.
    Proof.
    Admitted.

    (** Prove the max value wrt entangled costs of two states  *)
    Lemma Cost_max_ent : forall s s',
        \sum_(i : 'I_N) (cost i ((mixed_cost i s) s')) <= max_Cost /\ exists s', Cost s' = max_Cost.
    Proof.
    Admitted.

    Lemma Cost'_aux_max : forall p,
      Cost'_aux p <= N%:Q * (N%:Q - 2%:Q).
    Proof.
    Admitted.

    Lemma lem1 : forall (a : rat),
      (a - a / 2%:Q)%R = (a / 2%:Q)%R.
    Admitted.

    (** ler_trans won't apply directly to the goal in gen_smooth
        but it works indirectly by using this lemma *)
    Lemma q_le_trans : forall (a b c : rat),
      a <= b -> b <= c -> a <= c.
    Proof.
      move => a b c. apply ler_trans.
    Qed.

    (*********************************************************)
    (** Cost'_aux ((N-1) / 2) <= Cost'_aux (anything else) *)

    Lemma Camin1 : forall (a b c d : rat),
      a - c <= d - b -> a + b <= c + d.
    Admitted.

    Lemma Camin2 : forall p,
      (p * (p - 1))%R = p * p - p.
    Admitted.

    Lemma Camin3 : forall p p',
      (p * p - p) - (p' * p' - p') =
      p * p - p - p' * p' + p'.
    Admitted.

    Lemma Camin4 : forall p,
      ((N%:Q - p) * (N%:Q - 2%:Q))%R =
      N%:Q * N%:Q - 2%:Q * N%:Q - p * N%:Q + 2%:Q * p.
    Admitted.

    Lemma Camin5 : forall p p',
      (N%:Q * N%:Q - 2%:Q * N%:Q - p' * N%:Q + 2%:Q * p') -
      (N%:Q * N%:Q - 2%:Q * N%:Q - p * N%:Q + 2%:Q * p) =
      2%:Q * p' + p * N%:Q - 2%:Q * p - p' * N%:Q.
    Admitted.

    Lemma Camin6 : forall p p',
      (p * p - p - p' * p' + p' <=
       2%:Q * p' + p * N%:Q - 2%:Q * p - p' * N%:Q) =
      (p' * N%:Q - p' - p' * p' <= p * N%:Q - p - p * p).
    Admitted.

    Lemma Camin7 : forall p p',
      (p' * N%:Q - p' - p' * p' <= p * N%:Q - p - p * p) =
      (p' * (N%:Q - 1 - p') <= p * (N%:Q - 1 - p)).
    Admitted.

    Lemma Camin11 : forall p p',
      (p * (p - 1) - p' * (p' - 1) <=
      (N%:Q - p') * (N%:Q - 2%:Q) - (N%:Q - p) * (N%:Q - 2%:Q)) =
      (p' * (N%:Q - 1 - p') <= p * (N%:Q - 1 - p)).
    Proof.
      move => p p'.
      rewrite !Camin2 Camin3 !Camin4 Camin5 Camin6 Camin7 => //.
    Qed.

    (** the key lemma *)
    Lemma Camin12' : forall a b,
      0 <= a + b ->
      a * b <= ((a + b) / 2%:R) ^+ 2.
    Proof. by move=> a b H; rewrite (lerif_AGM2 a b). Qed.

    Lemma Camin12 : forall a b m,
      0 <= m ->
      a + b = m ->   
      a * b <= (m / 2%:Q) * (m / 2%:Q).
    Proof.
      move=> a b m H H2.
      apply: ler_trans.
      apply: Camin12'; first by rewrite H2.
      rewrite -H2.
      have H3: forall x : rat, x ^+ 2 = x * x by [].
      by rewrite H3.
    Qed.      
    
    Lemma Camin13 : 
      1 <= N%:Q -> 0%R <= (N%:Q - 1).
    Proof. 
    Admitted.

    Lemma Camin14 : forall a b,
      a + (b - a) = b.
    Proof.
      move => a b. rewrite addqC. rewrite -addqA.
      assert (- a + a = a - a). rewrite addqC => //.
      rewrite H. ring.
    Qed.

    Lemma Cost'_aux_min : forall p',
      1 <= N%:Q ->
      p' <= N%:Q - 1 ->
      Cost'_aux ((N%:Q - 1) / 2%:Q) <= Cost'_aux p'.
    Proof.
      move => p' H0 H1.
      remember (((N%:Q - 1) / 2%:Q)%R) as p.
      rewrite /Cost'_aux. apply Camin1. rewrite Camin11.
      assert ((p' * (N%:Q - 1 - p')) <= (((N%:Q - 1) / 2%:Q) * ((N%:Q - 1) / 2%:Q))).
      { apply Camin12. apply Camin13 => //. apply Camin14. }
      assert ((N%:Q - 1) / 2%:Q * ((N%:Q - 1) / 2%:Q) <= p * (N%:Q - 1 - p)).
      { rewrite Heqp. rewrite lem1 => //. }
      apply q_le_trans with (b:=(N%:Q - 1) / 2%:Q * ((N%:Q - 1) / 2%:Q)).
      { apply H. }
      apply H2.
    Qed.

    Lemma Cmin1 : forall s,
      (num_players_false s == N%:Q)%B = false ->
      num_players_false s <= N%:Q - 1.
    Admitted.

    Lemma Cost'_min : forall s,
      1 <= N%:Q ->
      Cost'_aux ((N%:Q - 1%:Q) / 2%:Q) <= Cost' s.
    Proof.
      move => s H. rewrite /Cost'.
      remember (((N%:Q - 1%:Q) / 2%:Q)%R) as p.
      (* case: (num_players_false s == N%:Q)%B. *)
      destruct ((num_players_false s == N%:Q)%B) eqn:HNumF.
      { apply Cost'_aux_max. }
      { rewrite Heqp. apply Cost'_aux_min => //.
        apply Cmin1. apply HNumF.
      }
    Qed.

    (*********************************************************)
    (** 2/3 * max <= min. *)

    (* might only work when N >= 3, do N = 2 separately in Cost_ratio *)
    Lemma min_max_ratio :
      2%:Q <= N%:Q ->
      (2%:Q/3%:Q) * max_Cost <= Cost'_aux ((N%:Q - 1) / 2%:Q).
    Admitted.

    Lemma le_2_N__le_1_N :
      2%:Q <= N%:Q ->
      1%:Q <= N%:Q.
    Proof.
      move => H. have H0: (1 <= 2%:Q) by [].
      apply: ler_trans. apply: H0. apply H.
Qed.

    (** Prove that the Cost wrt any state is no less than 2/3 the max. *)
    Lemma Cost_ratio : forall s,
      2%:Q <= N%:Q ->
      (2%:Q/3%:Q) * max_Cost <= Cost s.
    Proof.
      move => s H. rewrite Cost_equiv.
      assert ((2%:Q/3%:Q) * max_Cost <= Cost'_aux ((N%:Q - 1) / 2%:Q)) as H0.
      { apply min_max_ratio => //. }
      assert (Cost'_aux ((N%:Q - 1) / 2%:Q) <= Cost' s) as H1.
      { apply Cost'_min. apply le_2_N__le_1_N => //. }
      apply q_le_trans with (b := Cost'_aux ((N%:Q - 1) / 2%:Q)).
      apply H0.
      apply H1.
    Qed.

    Lemma gen_smooth : forall (s s' : bool ^ N),
        \sum_(i : 'I_N) (cost i) (mixed_cost i s s') <=
        lambda * (Cost s') + mu * (Cost s).
    Proof.
      rewrite /smooth /lambda /mu => s s'.
      (* Eliminate the mu term since it is zero *)
      assert ((0%:Q * Cost s)%R = 0%:Q) as H0.
        { apply mul0r. }
      rewrite H0. rewrite addqC. rewrite add0q.
      (* This follows directly from Cost_max_ent *)
      assert ((2%:Q/3%:Q) * (\sum_(i < N) cost i ((mixed_cost i s) s')) <=
              (2%:Q/3%:Q) * max_Cost) as H1.
      { apply ler_mull => //.
        apply Cost_max_ent.
      }
      (* This is the key fact that is necessary for the proof *)
      assert ((2%:Q/3%:Q) * max_Cost <= Cost s') as H2.
      { apply Cost_ratio. apply le_2_N. (* N >= 2 *) }
      (* Tf 2/3 the max is bounded above by Cost s',
         then so is 2/3 * (the mixed cost) *)
      assert ((2%:Q/3%:Q) * (\sum_(i < N) cost i ((mixed_cost i s) s')) <=
              Cost s') as H3.
      { apply q_le_trans with (b := 2%:Q / 3%:Q * max_Cost).
        apply H1. apply H2.
      }
      (* The goal now follows directly from H3 by algebra *)
      assert ((2%:Q / 3%:Q) * (\sum_(i < N) cost i ((mixed_cost i s) s')) <=
              (2%:Q / 3%:Q) * ((3%:Q / 2%:Q) * Cost s')) as H4.
      { rewrite -{-1} invf_div. rewrite mulqA.
        assert (((3%:Q / 2%:Q)^-1 * (3%:Q / 2%:Q)) = 1) as H5.
          apply mulVq => //.
        rewrite H5. rewrite mul1q. apply H3.
      }
      assert ((\sum_(i < N) (cost i ((mixed_cost i s) s'))) <=
       (3%:Q / 2%:Q * Cost s')) as H5.
        apply ler_mull2 in H4 => //.
      apply H5.
    Qed.

  End locationResidualGame.
End LocationResidualGame.

(* Module SmoothLocationResidualGame. *)
(*   Section smoothLocationResidualGame. *)
(*     Variable rty : realFieldType. *)
(*     Variable N : nat. *)
(*     Definition g := (LocationResidualGame.t rty N). *)
(*     Definition lambda : rty := 3%:R/2%:R. *)
(*     Definition mu : rty := 0. *)

(*     Lemma smoothness : *)
(*       @smooth_axiom g lambda mu. *)
(*         rewrite /smooth_axiom. move => t t' _. *)
(*         exact (LocationResidualGame.gen_smooth rty t t'). *)
(*     Qed. *)
    
(*     Instance t : @smooth g := mkSmooth smoothness. *)

(*   End smoothLocationResidualGame. *)
(* End SmoothLocationResidualGame. *)
