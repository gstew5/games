Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith Qreals Reals Fourier.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

(** This file defines conversions between Ssreflect/MathComp and
    Coq Standard Library implementations of various numeric types, 
    such as: 
      - int <-> Z
      - rat <-> Q
      - rat -> R
 *)

Section int_to_Z.
  Variable i : int.

  Definition int_to_positive : positive :=
    match i with
    | Posz n => Pos.of_nat n
    | Negz n => Pos.of_nat n
    end.

  Definition int_to_Z : Z :=
    match i with
    | Posz n => Z.of_nat n
    | Negz n => Z.neg (Pos.of_succ_nat n)
    end.

  Lemma posint_to_positive (H : (0 < i)%R) :
    Z.pos int_to_positive = int_to_Z.
  Proof.
    rewrite /int_to_positive /int_to_Z.
    case: i H=> //.
    move=> n H.
    rewrite -positive_nat_Z.
    f_equal.
    rewrite Nat2Pos.id=> //.
    by move=> H2; rewrite H2 in H.
  Qed.
End int_to_Z.

Lemma pos_of_succ_nat_mul n m :
  (Pos.of_succ_nat n * Pos.of_succ_nat m)%positive =
  Pos.of_succ_nat (m + (n * m.+1)%Nrec).
Proof.
  elim: n=> //=.
  by rewrite addn0.
  move=> n IH.
  rewrite Pos.mul_succ_l IH.
  rewrite -mulnE mulnS.
  rewrite 3!Pos.of_nat_succ.
  by rewrite -Nat2Pos.inj_add.
Qed.

Lemma opp_posz_negz (n : nat) : GRing.opp (Posz (n.+1)) = Negz n.
Proof. by elim: n. Qed.

Lemma pos_sub_pred p : Z.pos_sub p 1 = Z.pred (Z.pos p).
Proof.
  set (P := fun p0 => Z.pos_sub p0 1 = Z.pred (Z.pos p0)).
  change (P p).
  by apply: positive_ind.
Qed.  

Lemma pos_sub_succ1 m : 
  Z.pos_sub (Pos.of_succ_nat m.+1) 1 = Z.pos (Pos.of_succ_nat m).
Proof.
  rewrite pos_sub_pred.
  rewrite 2!Zpos_P_of_succ_nat.
  rewrite -!Zpred_succ /=.
  by rewrite Zpos_P_of_succ_nat.
Qed.

Lemma pos_sub_succ m n :  
  Z.pos_sub (Pos.succ (Pos.of_succ_nat m)) (Pos.of_succ_nat n) =
  Z.succ (Z.pos_sub (Pos.of_succ_nat m) (Pos.of_succ_nat n)).
Proof.
  rewrite -Pos2Z.add_pos_neg.
  rewrite Pos2Z.inj_succ.
  by rewrite Z.add_comm Z.add_succ_r.
Qed.

Lemma pos_sub_1succ n : 
  Z.pos_sub 1 (Pos.succ (Pos.of_succ_nat n)) =
  Z.neg (Pos.of_succ_nat n).
Proof.
  elim: n=> //= n IH.
  rewrite -Z.pos_sub_opp.
  rewrite -[Pos.succ (Pos.of_succ_nat n)]Pos2SuccNat.id_succ.
  by rewrite pos_sub_succ1.
Qed.
    
Lemma pos_of_succ_nat_sub n m :
  Z.pos_sub (Pos.of_succ_nat n) (Pos.of_succ_nat m) =
  int_to_Z (Posz n - Posz m).
Proof.
  elim: n m=> //= m.
  rewrite sub0r.
  case: m=> [//|m'].
  rewrite opp_posz_negz. simpl.
  rewrite -SuccNat2Pos.inj_succ.
  rewrite -Z.pos_sub_opp.
  rewrite -Pos2Z.opp_pos.
  f_equal.
  rewrite pos_sub_pred.
  rewrite Zpos_P_of_succ_nat.
  by rewrite -Zpred_succ.
  move=> IH n /=.
  rewrite pos_sub_succ.
  rewrite IH.
  rewrite /int_to_Z.
  rewrite intS.
  rewrite -addrA.
  case: (Posz m - Posz n)%R=> n'.
  { by rewrite /= Zpos_P_of_succ_nat. }
  move {IH m n}.
  elim: n'=> // n /= IH.
  have H: (subn n.+1 1 = n) by move {IH}; elim: n.
  by rewrite H pos_sub_1succ.
Qed.  

Lemma pos_of_succ_nat_plus n m : 
  (Pos.of_succ_nat n + Pos.of_succ_nat m)%positive =
  Pos.succ (Pos.of_succ_nat (n + m)).
Proof.
  elim: n m=> // m.
  rewrite add0n.
  rewrite Pos.of_nat_succ.
  by rewrite Pos.add_1_l.
  move=> IH m'.
  simpl.
  rewrite Pos.add_succ_l.
  by rewrite IH.
Qed.

Lemma int_to_Z_add_sub s r :
  int_to_Z (s + Negz r) = int_to_Z (s - (Posz r.+1)).
Proof. by elim: s. Qed.

Lemma int_to_Z_plus (s r : int) :
  Zplus (int_to_Z s) (int_to_Z r) = int_to_Z (s + r).
Proof.
  case: s=> sn.
  case: r=> rn.
  simpl.
  by rewrite -Nat2Z.inj_add.
  { simpl.
    rewrite /Z.of_nat.
    case: sn=> [|sn'].
    { by rewrite add0r Zplus_0_l. }
    rewrite Pos2Z.add_pos_neg.
    rewrite int_to_Z_add_sub.
    rewrite subzSS.
    by rewrite pos_of_succ_nat_sub.
  }
  case: r=> rn.
  { simpl.
    rewrite /Z.of_nat.
    case: rn=> [|rn'].
    by simpl; rewrite subn0.
    rewrite pos_of_succ_nat_sub.
    symmetry; rewrite addrC.
    rewrite int_to_Z_add_sub.
    by rewrite subzSS.
  }
  simpl.
  f_equal.
  by rewrite pos_of_succ_nat_plus.
Qed.

Lemma int_to_positive_mul (s r : int) :
  int_to_positive (s * r) = Pos.mul (int_to_positive s) (int_to_positive r).
Proof.
Admitted.

Lemma int_to_Z_mul (s r : int) :
  Zmult (int_to_Z s) (int_to_Z r) = int_to_Z (s * r).
Proof.
  case: s=> sn.
  case: r=> rn.
  simpl.
  by rewrite -Nat2Z.inj_mul.
  { simpl.
    rewrite /Z.of_nat.
    case: sn=> [//=|sn'].
    rewrite mulrC /=.
    f_equal.
    by rewrite pos_of_succ_nat_mul.
  }
  case: r=> rn.
  { simpl.
    rewrite /Z.of_nat.
    case: rn=> [//=|rn'].
    rewrite mulrC /=.
    f_equal.
    rewrite pos_of_succ_nat_mul.
    rewrite -mulnE.
    rewrite 2!mulnS.
    rewrite mulnC.
    rewrite addnA.
    rewrite [(rn' + sn)%N]addnC.
    by rewrite -addnA.
  }
  simpl.
  f_equal.
  by rewrite pos_of_succ_nat_mul.
Qed.

Lemma Zneg_Zlt r s :
  Pos.gt r s -> 
  Zlt (Zneg r) (Zneg s).
Proof.
  rewrite /Pos.gt.
  by rewrite /Z.lt /= => ->.
Qed.  

Lemma Zneg_Zle r s :
  Pos.ge r s -> 
  Zle (Zneg r) (Zneg s).
Proof.
  rewrite /Pos.ge /Z.le /= => H; rewrite /CompOpp.
  by move: H; case: (r ?= s)%positive.
Qed.

Lemma int_to_Z_lt (s r : int) :
  ltr s r ->
  Zlt (int_to_Z s) (int_to_Z r).
Proof.
  case: s=> sn; case: r=> rn //.
  { simpl.
    move=> H; apply: inj_lt.
    rewrite /ltr /= in H.
    by apply/leP.
  }
  { simpl=> H.
    have H2: (Z.lt (Z.neg (Pos.of_succ_nat sn)) 0).
    { by apply: Zlt_neg_0. }
    apply: Z.lt_le_trans.
    apply: H2.
      by apply: Zle_0_nat.
  }
  simpl.
  rewrite /ltr /= => H.
  apply: Zneg_Zlt.
  move: (inj_lt _ _ (leP H)).
  rewrite 2!Pos.of_nat_succ => H2.
  rewrite /Pos.gt.
  rewrite -Nat2Pos.inj_compare=> //.
  move: H.
  move/leP. 
  simpl.
  by rewrite Nat.compare_gt_iff.
Qed.  

Lemma int_to_Z_le (s r : int) :
  ler s r ->
  Zle (int_to_Z s) (int_to_Z r).
Proof.
  case: s=> sn; case: r=> rn //.
  { simpl.
    move=> H; apply: inj_le.
    by apply/leP.
  }
  { simpl=> H.
    have H2: (Z.le (Z.neg (Pos.of_succ_nat sn)) 0).
    { by apply: Pos2Z.neg_is_nonpos. }
    apply: Z.le_trans.
    apply: H2.
    by apply: Zle_0_nat.
  }
  simpl.
  rewrite /ler /= => H.
  apply: Zneg_Zle.
  move: (inj_le _ _ (leP H)).
  rewrite 2!Pos.of_nat_succ => H2.
  rewrite /Pos.ge.
  rewrite -Nat2Pos.inj_compare=> //.
  move: H.
  move/leP. 
  simpl.
  by rewrite Nat.compare_ge_iff.
Qed.  

Section rat_to_Q.
  Variable r : rat.
  
  Definition rat_to_Q : Q :=
    let: (n, d) := valq r in
    Qmake (int_to_Z n) (int_to_positive d).
End rat_to_Q.

Section rat_to_Q_lemmas.
  Local Open Scope ring_scope.
  Delimit Scope R with R_ssr.  
  Delimit Scope R_scope with R.

  Lemma rat_to_Q_fracq_pos (x y : int) :
    0 < y -> 
    Qeq (rat_to_Q (fracq (x, y))) (int_to_Z x # int_to_positive y).
  Proof.
    move=> H.
    rewrite /fracq /rat_to_Q /=.
    have ->: (y == 0) = false.
    { admit. }
    rewrite -int_to_Z_mul.
    have ->: y < 0 = false.
    { admit. }
    simpl.
    case H2: (x < 0).
    { rewrite /nat_of_bool.
      rewrite expr1z.
      rewrite /Qeq /Qnum /Qden.
      rewrite posint_to_positive => //.
      admit. }
    rewrite /nat_of_bool /Qeq /Qnum /Qden expr0z.
    admit.
  Admitted.  
    
  Lemma rat_to_Q_plus (r s : rat) :
    Qeq (rat_to_Q (r + s)) (Qplus (rat_to_Q r) (rat_to_Q s)).
  Proof.
    rewrite /GRing.add /= /addq /addq_subdef.
    case: r; case=> a b /= H.
    case: s; case=> c d /= H2.
    have H3: (0 < b * d).
    { case: (andP H) => X _.
      case: (andP H2) => Y _.
      apply: mulr_gt0 => //. }
    rewrite rat_to_Q_fracq_pos => //.
    rewrite /rat_to_Q /=.
    rewrite /Qplus /=.
    rewrite int_to_positive_mul.
    rewrite -int_to_Z_plus.
    rewrite -2!int_to_Z_mul.
    rewrite posint_to_positive.
    rewrite posint_to_positive.
    by [].
    by case: (andP H).
    by case: (andP H2).
  Qed.      
  
  Lemma rat_to_Q_mul (r s : rat) :
    Qeq (rat_to_Q (r * s)) (Qmult (rat_to_Q r) (rat_to_Q s)).
  Proof.
    rewrite /GRing.mul /= /mulq /mulq_subdef /=.
    case: r; case => a b /= i.
    case: s; case => a' b' /= i'.
    have H3: (0 < b * b').
    { case: (andP i) => X _.
      case: (andP i') => Y _.
      apply: mulr_gt0 => //. }
    rewrite rat_to_Q_fracq_pos => //.
    rewrite /rat_to_Q /=.
    rewrite /Qmult /=.
    rewrite int_to_positive_mul.
    by rewrite -int_to_Z_mul.
  Qed.      
End rat_to_Q_lemmas.    

Section rat_to_R.
  Variable r : rat.

  Definition rat_to_R : R := Q2R (rat_to_Q r).
End rat_to_R.

Section rat_to_R_lemmas.
  Local Open Scope ring_scope.
  Delimit Scope R_scope with R.
  
  Lemma rat_to_R0 : rat_to_R 0 = 0%R.
  Proof. by rewrite /rat_to_R /rat_to_Q /= /Q2R /= Rmult_0_l. Qed.

  Lemma rat_to_R1 : rat_to_R 1 = 1%R.
  Proof. by rewrite /rat_to_R /rat_to_Q /= /Q2R /= Rmult_1_l Rinv_1. Qed.

  Lemma rat_to_R2 : rat_to_R 2%:R = 2%R.
  Proof. by rewrite /rat_to_R /rat_to_Q /= /Q2R /= Rinv_1 Rmult_1_r. Qed.
  
  Lemma rat_to_R_lt (r s : rat) :
    lt_rat r s ->
    (rat_to_R r < rat_to_R s)%R.
  Proof.
    move=> H.
    rewrite /rat_to_R /rat_to_Q /=.
    apply: Qlt_Rlt.
    rewrite /Qlt.
    case: r H; case=> r1 r2 /= H1.
    case: s; case=> s1 s2 /= H2.
    rewrite /lt_rat /numq /denq /= => H3.
    case: (andP H1)=> H1a _.
    case: (andP H2)=> H2a _.
    rewrite !posint_to_positive=> //.
    rewrite 2!int_to_Z_mul.
    by apply: int_to_Z_lt.
  Qed.

  Lemma rat_to_R_le (r s : rat) :
    le_rat r s ->
    (rat_to_R r <= rat_to_R s)%R.
  Proof.
    move=> H.
    rewrite /rat_to_R /rat_to_Q /=.
    apply: Qle_Rle.
    rewrite /Qle.
    case: r H; case=> r1 r2 /= H1.
    case: s; case=> s1 s2 /= H2.
    rewrite /le_rat /numq /denq /= => H3.
    case: (andP H1)=> H1a _.
    case: (andP H2)=> H2a _.
    rewrite !posint_to_positive=> //.
    rewrite 2!int_to_Z_mul.
    by apply: int_to_Z_le.
  Qed.

  Lemma rat_to_R_plus (r s : rat) :
    rat_to_R (r + s) = (rat_to_R r + rat_to_R s)%R.
  Proof.
    rewrite /rat_to_R.
    rewrite -Q2R_plus.
    apply: Qeq_eqR.
    apply: rat_to_Q_plus.
  Qed.

  Lemma rat_to_R_mul (r s : rat) :
    rat_to_R (r * s) = (rat_to_R r * rat_to_R s)%R.
  Proof.
    rewrite /rat_to_R.
    rewrite -Q2R_mult.
    apply: Qeq_eqR.
    by apply: rat_to_Q_mul.
  Qed.

  Lemma rat_to_R_inv (r : rat) : rat_to_R r^-1 = Rinv (rat_to_R r).
  Admitted.

  Lemma rat_to_R_opp (r : rat) : rat_to_R (- r) = Ropp (rat_to_R r).
  Admitted.
End rat_to_R_lemmas.