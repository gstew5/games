Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Theory Num.Def.
Require Import QArith.

Require Import games.

Local Open Scope ring_scope.

Module Christodoulou.

  (* ########################################################### *)
  (** * Helper lemmas *)

  Lemma subrr' (rty : realFieldType) (a : rty) :
    - a + a = 0.
  Proof.
    rewrite addrC. apply: subrr.
  Qed.

  Lemma sub_add_0 (rty : realFieldType) (a b : rty) :
    a - b + b = a.
  Proof.
    rewrite -addrA subrr' addrC add0r => //.
  Qed.

  Lemma leq_case (a b : nat) :
    is_true (leq a (S b)) ->
    a = S b \/ is_true (leq a b).
  Proof.
    move => H. rewrite leq_eqVlt in H.
    move: H. move => /orP H.
    destruct H.
    left. move: H. move => /eqP H. apply H.
    right. apply H.
  Qed.

  (* ########################################################### *)
  (** * Subresult proof.

    yz <= y^2 + (1/3)z^2 *)

  (* Multiply both sides by 3 *)
  Lemma s1 (y z : nat) :
    3%:Q * y%:Q * z%:Q <= 3%:Q * y%:Q ^+ 2 + z%:Q ^+ 2 ->
    y%:Q * z%:Q <= (3%:Q / 3%:Q) * y%:Q ^+ 2 + (1%:Q / 3%:Q) * z%:Q ^+ 2.
  Proof.
    move => H0. apply ler_mull2 with (z := 3%:Q); auto. 
    rewrite mulrA [3%:~R * (_ + _)] mulrDr mulrA.
    have H1: ((3%:Q / 3%:Q) = 1%:Q) by apply: divff.
    rewrite H1 mulr1 mulrA mulrA mulrA.
    have H2: (3%:Q * (1%:Q / 3%:Q) = 1%:Q) by [].
    rewrite H2 mul1r.
    have H3: (y%:Q ^+ 2 = y%:Q * y%:Q) by [].
    have H4: (z%:Q ^+ 2 = z%:Q * z%:Q) by [].
    rewrite H3 H4 mulrA in H0. apply H0.
  Qed.

  (* Subtract 3*y^2 from both sides *)
  Lemma s2 (y z : nat) :
    (3%:Q * y%:Q * z%:Q - 3%:Q * y%:Q ^+ 2 <= z%:Q ^+ 2) ->
    (3%:Q * y%:Q * z%:Q <= 3%:Q * y%:Q ^+ 2 + z%:Q ^+ 2).
  Proof.
    move => H.
    have H0: (3%:Q * y%:Q * z%:Q - 3%:Q * y%:Q ^+ 2 +
              3%:Q * y%:Q ^+ 2 <= z%:Q ^+ 2 + 3%:Q * y%:Q ^+ 2).
    { apply ler_add. apply H. auto. }
    rewrite sub_add_0 addrC in H0. apply H0.
  Qed.

  (* Distrbute 3*y *)
  Lemma s3 (y z : nat) :
    3%:Q * y%:Q * z%:Q - 3%:Q * y%:Q ^+ 2 =
    3%:Q * y%:Q * (z%:Q - y%:Q).
  Proof. rewrite [_ * (_ - y%:Q)] mulrBr mulrA => //. Qed.

  (* Divide both sides by 3 *)
  Lemma s4 (y z : nat) :
    y%:Q * (z%:Q - y%:Q) <= (z%:Q / 2%:Q) ^+ 2 ->
    3%:Q * y%:Q * (z%:Q - y%:Q) <= 3%:Q * (z%:Q / 2%:Q) ^+ 2.
  Proof.
    move => H.
    have H0: (3%:Q * y%:Q * (z%:Q - y%:Q) = 3%:Q * (y%:Q * (z%:Q - y%:Q))).
    { rewrite mulrA => //. }
    rewrite H0.
    apply ler_mull => //.
  Qed.

  Lemma s5 (y z : nat) :
    z%:Q = y%:Q + (z%:Q - y%:Q).
  Proof. rewrite addrC sub_add_0 => //. Qed.

  (* Divide both sides by 3 then apply AGM inequality *)
  Lemma s6 (y z : nat) :
    3%:Q * y%:Q * (z%:Q - y%:Q) <= 3%:Q * (z%:Q / 2%:Q) ^+ 2.
  Proof.
    apply: s4.
    have H: (z%:Q = y%:~R + (z%:~R - y%:~R)) by apply: s5.
    rewrite {2} H.
    apply: lerif_AGM2.
  Qed.

  Lemma s7 (z : nat) :
    (z%:Q / 2%:Q) * (z%:Q / 2%:Q) = (z%:Q * z%:Q) / 4%:Q.
  Proof.
    have H0: (4%:Q = 2%:Q * 2%:Q) by [].
    rewrite H0 mulrA [z%:~R * z%:~R / _] mulrC.
    rewrite -mulrA -mulrA [2%:~R^-1 * _] mulrC mulrC.
    rewrite [z%:~R / 2%:~R] mulrC mulrA mulrA [2%:~R^-1 / 2%:~R] mulrC.
    rewrite -invrM; auto.
    rewrite mulrC [z%:~R / (2%:~R * 2%:~R) * z%:~R] mulrC mulrA => //.
  Qed.

  Lemma s8 (z : nat) :
    3%:Q * (z%:Q / 2%:Q) * (z%:Q / 2%:Q) =
    z%:Q * z%:Q * (3%:Q / 4%:Q).
  Proof.
    rewrite -[3%:Q * _ * _] mulrA s7 mulrA mulrC.
    rewrite [4%:~R^-1 * _] mulrA mulrC mulrC => //.
  Qed.

  (* 1 <= y -> 0 < y *)
  Lemma s9 (rty : numDomainType) (z : nat) :
    leq (S O) z ->
    0 < (z%:R^-1 : rty).
  Proof.
    rewrite -(ler_nat rty) => H.
    rewrite invr_gt0.
    have H2: (0 : rty) < 1%:R by [].
      by apply: (ltr_le_trans H2 H).
  Qed.

  (* 1 <= z -> z != 0 *)
  Lemma s10 (rty : numDomainType) (z : nat) :
    leq (S O) z -> 
    (z%:R : rty) != (0%:R : rty).
  Proof.
    move => H. rewrite -(ler_nat rty) in H.
    rewrite lt0r_neq0 => //.
    have H0: ((0 : rty) < (1%:R : rty)) by [].
      by apply: (ltr_le_trans H0 H).
  Qed.

  Lemma s11 (y z : nat) :
    3%:Q * (z%:Q / 2%:Q) ^+ 2 <= z%:Q ^+ 2.
  Proof.
    case H0: z.
    - (* z = 0 *)
      rewrite mul0r.
      have H1: (0%:Q ^+ 2 = 0%:Q * 0%:Q) by [].
        by rewrite !H1 mul0r mulrC mul0r.
    - (* z > 0 *)
      have H1: ((z%:Q / 2%:Q) ^+ 2 = (z%:Q / 2%:Q) * (z%:Q / 2%:Q)) by [].
      rewrite H0 in H1.
      rewrite H1 mulrA s8.
      have H2: (z%:Q ^+ 2 = z%:Q * z%:Q) by [].
      rewrite H0 in H2. rewrite H2.
      apply ler_mull2 with (z := z%:Q^-1). apply s9 => //; last by rewrite H0.
      rewrite -H0 [z%:Q^-1 * _] mulrA [z%:~R^-1 * _] mulrA [z%:~R^-1 * z%:~R] mulVf.
      rewrite mul1r.
      apply ler_mull2 with (z := z%:Q^-1). apply s9 => //.
        by rewrite H0.
        rewrite [z%:~R^-1 * _] mulrA [z%:~R^-1 * z%:~R] mulVf.
        rewrite  mul1r => //.
        apply s10 => //. by rewrite H0.
        apply s10 => //. by rewrite H0.
  Qed.

  (* this implies the main result when y >= 2 *)
  Lemma subresult (y z : nat) :
      y%:Q * z%:Q <=
      (3%:Q / 3%:Q) * y%:Q ^+ 2 + (1%:Q / 3%:Q) * z%:Q ^+ 2.
  Proof.
    apply: s1. apply: s2. rewrite s3.
    have H1: (3%:Q * y%:Q * (z%:Q - y%:Q) <= 3%:Q * (z%:Q / 2%:Q) ^+ 2)
      by apply: s6.
    have H2: (3%:Q * (z%:Q / 2%:Q) ^+ 2 <= z%:Q ^+ 2) by apply: s11.
    apply: ler_trans. apply H1. apply H2.
  Qed.

  (* ########################################################### *)
  (** * Subresult implies main result proof *)

  (* 2 <= y -> 0 < y *)
  Lemma sr3 (y : nat) :
    leq 2 y ->
    0 < y%:Q.
  Proof.
    move => H0.
    rewrite -(ltr1n rat_numDomainType) in H0.
    have H1: (0%:Q < 1%:Q) by [].
    apply: ltr_trans. apply H1. apply H0.
  Qed.

  (* 2 <= y -> 2/3 <= y *)
  Lemma sr4 (y : nat) :
    leq 2 y ->
    3%:Q / 2%:Q <= y%:Q.
  Proof.
    move => H0.
    rewrite -(ler_nat rat_numDomainType) in H0.
    have H1: (3%:Q / 2%:Q <= 2%:Q) by [].
    apply: ler_trans. apply: H1. apply: H0.
  Qed.

  (* 2 <= y -> y <= (2/3)*y^2 *)
  Lemma sr5 (y : nat) :
    leq 2 y ->
    y%:Q <= 2%:Q / 3%:Q * y%:Q ^+ 2.
  Proof.
    move => H.
    rewrite mulrC.
    have H0: (y%:Q ^+ 2 = y%:Q * y%:Q) by [].
    rewrite H0 mulrA.
    have H1: (y%:Q = y%:Q * 1%:Q). rewrite mulrC mul1r => //.
    rewrite {1} H1.
    have H2: (y%:Q * y%:Q * (2%:Q / 3%:Q) = y%:Q * (y%:Q * (2%:Q / 3%:Q)))
      by rewrite -mulrA.
    rewrite -mulrA  H2.
    apply ler_mull with (x := 1%:Q) (y := y%:Q * (2%:Q / 3%:Q)) (z := y%:Q).
    apply sr3 => //.
    apply ler_mull2 with (z := 3%:Q / 2%:Q) => //.
    rewrite mulrC mul1r.
    have H3: (y%:Q * (2%:Q / 3%:Q) = 2%:Q / 3%:Q * y%:Q) by rewrite mulrC.
    rewrite H3 mulrA.
    have H4: (2%:Q / 3%:Q = (3%:Q / 2%:Q)^-1) by [].
    have H5: (3%:Q / 2%:Q * (2%:Q / 3%:Q) = 1) by rewrite mulrC H4 mulVr.
    rewrite H5 mul1r.
    apply sr4 => //.
  Qed.

  (* Combine terms *)
  Lemma sr6 (y : nat) (a : rat) :
    3%:Q / 3%:Q * y%:Q ^+ 2 + a + 2%:Q / 3%:Q * y%:Q ^+ 2 =
    5%:Q / 3%:Q * y%:Q ^+ 2 + a.
  Proof.
    rewrite addrC addrA -mulrDl.
    have H: (2%:Q / 3%:Q + 3%:Q / 3%:Q = 5%:Q / 3%:Q) by [].
    rewrite H => //.
  Qed.

  (* When 2 <= y, subresult -> main result *)
  Lemma subresult_implies_result (y z: nat) :
      leq 2 y ->
      y%:Q * z%:Q <= (3%:Q / 3%:Q) * y%:Q ^+ 2 + (1%:Q / 3%:Q) * z%:Q ^+ 2 ->
      y%:Q * (z%:Q + 1) <= (5%:Q / 3%:Q) * y%:Q ^+ 2 + (1%:Q / 3%:Q) * z%:Q ^+ 2.
  Proof.
    move => H0 H1.
    have H2: (y%:Q * z%:Q + y%:Q <=
              3%:Q / 3%:Q * y%:Q ^+ 2 +
              1%:Q / 3%:Q * z%:Q ^+ 2 + (2%:Q / 3%:Q) * y%:Q ^+ 2).
    {  apply ler_add. apply H1. apply: sr5 => //. }
    rewrite sr6 in H2.
    rewrite mulrDr mulr1. apply: H2.
  Qed.

  (* 3 <= z -> z <= (1/3)*z^2 *)
  Lemma r1_1 (z : nat) :
    leq 3 z ->
    z%:Q <= 1%:Q / 3%:Q * z%:Q ^+ 2.
  Proof.
    move => H.
    rewrite mulrC.
    have H0: (z%:Q ^+ 2 = z%:Q * z%:Q) by [].
    rewrite H0 mulrA.
    have H1: (z%:Q = z%:Q * 1%:Q). rewrite mulrC mul1r => //.
    rewrite {1} H1.
    have H2: (z%:Q * z%:Q * (1%:Q / 3%:Q) = z%:Q * (z%:Q * (1%:Q / 3%:Q)))
      by rewrite -mulrA.
    rewrite -mulrA  H2.
    apply ler_mull with (x := 1%:Q) (y := z%:Q * (1%:Q / 3%:Q)) (z := z%:Q).
    apply sr3 => //.
    have H3: (ltn (S O) 2) by [].
    apply: ltn_trans. apply H3. apply H.
    apply ler_mull2 with (z := 3%:Q / 1%:Q).
    rewrite mulrC mul1r => //.
    have H3: (z%:Q * (1%:Q / 3%:Q) = 1%:Q / 3%:Q * z%:Q) by rewrite mulrC.
    rewrite H3 mulrA.
    have H4: (1%:Q / 3%:Q = (3%:Q / 1%:Q)^-1) by [].
    have H5: (3%:Q / 1%:Q * (1%:Q / 3%:Q) = 1) by rewrite mulrC H4 mulVr.
    rewrite H5 mul1r mulrC mul1r.
    have H6: (3%:Q / 1%:Q = 3%:Q) by []. rewrite H6.
    rewrite ler_nat. apply H.
  Qed.

  (* This is the main result when y = 1 *)
  Lemma r1 (z : nat) :
      z%:Q + 1 <= 5%:Q / 3%:Q + 1%:Q / 3%:Q * z%:Q ^+ 2.
  Proof.
    have H0: (z%:Q <= 2%:Q / 3%:Q +  1%:Q / 3%:Q * z%:Q ^+ 2).
    { case H: (leq 3 z).
      apply elimT with (P := (le 3 z)%N) in H.
      rewrite addrC.
      have H0: (z%:Q = z%:Q + 0%:Q) by rewrite addrC add0r => //.
      rewrite {1} H0. apply ler_add; auto.
      apply r1_1. move: H. move => /leP => //.
      apply /leP.
      apply negbT in H.  rewrite -ltnNge in H.
      apply leq_case in H. destruct H.
      have H1: (z = 2) by omega. rewrite H1 => //.
      apply leq_case in H. destruct H.
      have H1: (z = S O) by omega. rewrite H1 => //.
      apply leq_case in H. destruct H.
      have H1: (z = O) by omega. rewrite H1 => //.
      rewrite ltn0 in H. congruence. }
    have H1: (5%:Q / 3%:Q = 2%:Q / 3%:Q + 1%:Q) by [].
    rewrite H1 -addrA [1%:~R + _] addrC addrA.
    apply ler_add; by [].
  Qed.

  (* ########################################################### *)
  (** * Main result *)

  Lemma result (y z : nat) :
      y%:Q * (z%:Q + 1) <=
      (5%:Q / 3%:Q) * y%:Q ^+ 2 + (1%:Q / 3%:Q) * z%:Q ^+ 2.
  Proof.
    case H: (leq 2 y).
    - (* y > 1 *)
      apply: subresult_implies_result => //.
      apply: subresult.
      (* other cases *)
      apply negbT in H. rewrite -leqNgt in H.
      apply leq_case in H. destruct H.
      + (* y = 1 *)
        rewrite H. rewrite mul1r. apply: r1.
      + (* y = 0*)
        rewrite leqn0 in H. move: H. move => /eqP H.
        rewrite H mul0r mulrC mul0r add0r.
        apply: mulr_ge0 => //. apply: sqr_ge0.
  Qed.

End Christodoulou.
