Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith Reals Rpower Ranalysis Fourier.
Require Import Coq.Logic.ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema dist numerics neps_exp_le.

Section weights.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A is inhabited*)
  Variable eps : rat.
  Variable eps_range : 0 < eps <= 1/2%:R.
    
  Definition weights := {ffun A -> rat}.
  Definition init_weights : weights := finfun (fun _ => 1%:R).
  Definition costs := {ffun A -> rat}. 

  Lemma init_weights_gt0 :
    forall a : A, 0 < init_weights a.
  Proof. by move=> a; rewrite /init_weights ffunE. Qed.
  
  Definition update_weights (w : weights) (c : costs) : weights :=
    finfun (fun a : A => w a * (1 - eps * c a)).

  Lemma update_weights_gt0 (w : weights) (c : costs) :
    (forall a : A, 0 <= c a <= 1) -> 
    (forall a : A, 0 < w a) ->
    forall a : A, 0 < update_weights w c a.
  Proof.
    move=> H0 H a.
    rewrite /update_weights ffunE.
    apply: mulr_gt0=> //.
    rewrite subr_gt0.
    case: (andP eps_range)=> H1 H2.
    rewrite mulrC.
    case H3: (c a == 0).
    { move: (eqP H3)=> ->; rewrite mul0r=> //.
    }
    have H4: (c a * eps < c a).
    rewrite gtr_pmulr.
    apply: (ler_lt_trans H2)=> //.
    case: (andP (H0 a))=> H4 H5.
    rewrite lt0r; apply/andP; split=> //.
    by apply/eqP=> H6; rewrite H6 in H3.
    by apply: (ltr_le_trans H4); case: (andP (H0 a)).
  Qed.    

  (** The cost functions [cs] are given in reverse chronological order.
      That is, 
        [cs = c_T :: c_(T-1) :: ... :: c_1].
      This simplifies reasoning: [weights_of] is now fold-right
      rather than fold-left. *)
  Fixpoint weights_of (cs : seq costs) (w : weights) : weights :=
    if cs is [:: c & cs'] then
      update_weights (weights_of cs' w) c
    else w.

  Lemma weights_of_ind
        (cs : seq costs)
        (w : weights)
        (P : seq costs -> weights -> Prop) :
    P [::] w ->
    (forall w' c cs',
        P cs' w' ->
        P [:: c & cs'] (update_weights w' c)) ->
    P cs (weights_of cs w).
  Proof.
    move=> H IH; elim: cs=> //.
    move=> c cs' H0 /=.
    by apply: IH.
  Qed.    

  Lemma weights_of_eq (cs : seq costs) :
    weights_of cs init_weights =
    finfun (fun a => \prod_(c <- cs) (1 - eps*(c a))).
  Proof.
    elim: cs.
    { simpl.
      rewrite /init_weights.
      apply/ffunP=> x.
      by rewrite !ffunE big_nil.
    }
    move=> a l H /=.
    rewrite /update_weights; apply/ffunP=> x; rewrite H !ffunE.
    by rewrite big_cons mulrC.
  Qed.    
    
  Lemma weights_of_gt0 (cs : seq costs) (w : weights) :
    (forall c, c \in cs -> forall a : A, 0 <= c a <= 1) ->     
    (forall a : A, 0 < w a) -> 
    forall a : A, 0 < weights_of cs w a.
  Proof.
    apply weights_of_ind=> //.
    move=> w' c cs' IH H0 H1 a.
    apply: update_weights_gt0=> //.
    by apply: H0; rewrite /in_mem /=; apply/orP; left.
    apply: IH=> // c0 Hin a1.
    by apply: H0; rewrite /in_mem /=; apply/orP; right.
  Qed.   

  Lemma sum_gt0 (w : weights) :
    (forall a : A, 0 < w a) ->
    0 < \sum_(a : A) w a.
  Proof.
    move=> H0.
    have H: 0 <= \sum_(a : A) w a.
    { by apply/sumr_ge0=> i _; apply/ltrW. }
    rewrite ltr_def; apply/andP; split=> //.
    apply/eqP=> H1.
    have H2: forall i : A, true -> 0 <= w i.
    { by move=> i _; apply/ltrW. }
    move: (psumr_eq0P (P:=xpredT)(F:=w) H2 H1).
    move: (H0 a0)=> H4.
    by move/(_ a0 erefl)=> H3; rewrite H3 in H4.
  Qed.
  
  Lemma sum_weights_of_gt0 (cs : seq costs) (w : weights) :
    (forall c, c \in cs -> forall a : A, 0 <= c a <= 1) ->     
    (forall a : A, 0 < w a) -> 
    0 < \sum_(a : A) (weights_of cs w) a.
  Proof.
    by move=> H0 H; apply: sum_gt0; apply: weights_of_gt0.
  Qed.   
 
  Lemma sum_weights_of_not0 (cs : seq costs) :
    (forall c, c \in cs -> forall a : A, 0 <= c a <= 1) ->     
    \sum_(a : A) (weights_of cs init_weights) a != 0.    
  Proof.
    move=> H; move: sum_weights_of_gt0.
    move/(_ cs init_weights H init_weights_gt0)=> H0.
    by apply/eqP=> H1; rewrite H1 in H0.
  Qed.    

  Lemma weight1_sum_ler (a : A) (w : weights) :
    (forall a : A, 0 <= w a) ->
    w a <= \sum_(a0 : A) w a0.
  Proof.
    move=> H.
    suff: ((\sum_(a1 : A) if a1 == a then w a1 else 0) <= \sum_a1 w a1).
    { move=> H2.
      have H3: w a <= \sum_a1 (if a1 == a then w a1 else 0).
      { have H4: \sum_a1 (if a1 == a then w a1 else 0) = \sum_(a1 | a1 == a) w a1.
        { by rewrite -big_mkcond.
        }
        by rewrite H4 big_pred1_eq.
      }
      by apply: (ler_trans H3 H2).
    }
    apply: ler_sum.
    by move=> i _; case: (i == a).
  Qed.

  Definition gamma (w : weights) : rat :=
    \sum_(a : A) (w a).

  Lemma gamma_normalizes (w : weights) :
    \sum_(a : A) w a != 0 -> 
    \sum_(a : A) w a / gamma w == 1.
  Proof. by move=> H; rewrite /gamma -mulr_suml mulrC mulVf. Qed.

  Lemma gamma_ge0 (w : weights) :
    (forall a : A, 0 <= w a) -> 
    0 <= gamma w.
  Proof.
    by move=> H; apply: sumr_ge0.
  Qed.
    
  Definition p_aux (cs : seq costs) (w : weights) : weights :=
    let w' := weights_of cs w in
    finfun (fun a : A => w' a / gamma w').

  Lemma div1rr (r : rat) : r != 0 -> 1 / r * r == 1.
  Proof. by move=> H; rewrite div1r mulVf. Qed.

  Lemma div1rn (n : nat) (r : rat) : r != 0 -> r == n%:R -> 1 / r *+ n == 1.
  Proof.
    move=> H H2; move: (eqP H2)=> H3.
    rewrite H3 -mulrnAl mulfV=> //.
      by rewrite -H3.
  Qed.

  Lemma Acard_gt0 : (0 < #|A|)%N.
  Proof. by apply/card_gt0P; exists a0. Qed.

  Lemma rat_to_R_Acard_gt0 : Rlt 0 (rat_to_R #|A|%:R).
  Proof.
    move: Acard_gt0; rewrite -rat_to_R0 -(@ltr_nat rat_numDomainType).
    by apply: rat_to_R_lt.
  Qed.
  
  Lemma p_aux_ind
        (cs : seq costs)
        (w : weights)
        (CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1)
        (WEIGHTS : forall a : A, 0 < w a)        
        (P : seq costs -> weights -> Prop) :
    P [::] [ffun a => w a / gamma w] ->
    (forall (w' : weights) c cs',
        let: w'' := update_weights w' c in
        (forall a : A, 0 <= c a <= 1) ->
        (forall a : A, 0 < w' a) -> 
        P cs' [ffun a => w' a / gamma w'] ->
        P [:: c & cs'] [ffun a => w'' a / gamma w'']) -> 
    P cs (p_aux cs w).
  Proof.
    move=> H IH; elim: cs CMAX=> //.
    move=> c cs'; rewrite /p_aux /=.
    set w' := weights_of cs' w.
    move=> H0 H1; apply: (IH w' c cs').
    by apply: H1; rewrite /in_mem /=; apply/orP; left.
    apply: weights_of_gt0=> // cx Hin a; apply: H1.
    by rewrite /in_mem /=; apply/orP; right.
    by apply: H0=> c0 H2 a; apply: H1; rewrite /in_mem /=; apply/orP; right.
  Qed.    
  
  Definition p (cs : seq costs) : {ffun A -> rat} :=
    p_aux cs init_weights.

  Lemma p_dist_axiom (cs : seq costs) :
    (forall c, c \in cs -> forall a : A, 0 <= c a <= 1) -> 
    dist_axiom (p cs).
  Proof.
    move=> H0; rewrite /p /dist_axiom; apply/andP; split.
    { rewrite /p_aux.
      have H:
        \sum_(t : A)
         [ffun a => (weights_of cs init_weights) a /
                    gamma (weights_of cs init_weights)] t
      = \sum_(t : A)
         (weights_of cs init_weights) t /
         gamma (weights_of cs init_weights).
      { by apply/congr_big=> // i _; rewrite ffunE. }
      rewrite H; move {H}.
      rewrite gamma_normalizes=> //.
      by apply: sum_weights_of_not0.
    }
    apply (p_aux_ind H0 init_weights_gt0).
    { apply/forallP=> x; rewrite ffunE.
      apply: mulr_ge0; first by rewrite /init_weights ffunE.
      rewrite invr_ge0 /gamma /init_weights; apply/sumr_ge0=> i _.
      by rewrite ffunE.
    }
    move=> w' c cs' H1 H2 H3; apply/forallP=> x; rewrite ffunE.
    have H4: forall a : A, 0 < update_weights w' c a.
    { move=> a; apply: update_weights_gt0=> //. }
    apply: divr_ge0; first by apply/ltrW; apply: (H4 x).
    by apply: gamma_ge0=> a; apply/ltrW.
  Qed.

  Delimit Scope R_scope with R.

  Fixpoint big_sum (T : Type) (cs : seq T) (f : T -> R) : R :=
    if cs is [:: c & cs'] then (f c + big_sum cs' f)%R
    else 0%R.

  Lemma big_sum_nmul (T : Type) (cs : seq T) (f : T -> R) :
    (big_sum cs (fun c => - f c) = - big_sum cs [eta f])%R.
  Proof.
    elim: cs=> /=; first by rewrite Ropp_0.
    by move=> a l IH; rewrite Ropp_plus_distr IH.
  Qed.      

  Lemma big_sum_ext T (cs cs' : seq T) f f' :
    cs = cs' -> f =1 f' -> big_sum cs f = big_sum cs' f'.
  Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

  Lemma big_sum_scalar T (cs : seq T) r f :
    (big_sum cs (fun c => r * f c) = r * big_sum cs (fun c => f c))%R.
  Proof.
    elim: cs=> /=; first by rewrite Rmult_0_r.
    by move=> a l IH; rewrite IH /=; rewrite Rmult_plus_distr_l.
  Qed.      
  
  Fixpoint big_product (T : Type) (cs : seq T) (f : T -> R) : R :=
    if cs is [:: c & cs'] then (f c * big_product cs' f)%R
    else 1%R.
  
  Lemma big_product_ext T (cs cs' : seq T) f f' :
    cs = cs' -> f =1 f' -> big_product cs f = big_product cs' f'.
  Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

  Lemma big_product_ge0 (T : eqType) (cs : seq T) (f : T -> R) :
    (forall c, c \in cs -> 0 <= f c)%R ->
    (0 <= big_product cs f)%R.
  Proof.
    elim: cs=> /=.
    { move=> _; apply: Fourier_util.Rle_zero_1. }
    move=> a l IH H.
    have H2: (0 = 0 * 0)%R by rewrite Rmult_0_l.
    rewrite H2; apply: Rmult_le_compat.
    by apply: Rle_refl.
    by apply: Rle_refl.
    by apply: H; rewrite in_cons; apply/orP; left.
    apply: IH=> c H3; apply: H.
    by rewrite in_cons; apply/orP; right.
  Qed.

  Lemma big_product_gt0 (T : eqType) (cs : seq T) (f : T -> R) :
    (forall c, c \in cs -> 0 < f c)%R ->
    (0 < big_product cs f)%R.
  Proof.
    elim: cs=> /=.
    { move=> _; apply: Fourier_util.Rlt_zero_1. }
    move=> a l IH H.
    have H2: (0 = 0 * 0)%R by rewrite Rmult_0_l.
    apply: Rmult_lt_0_compat.
    by apply: H; rewrite in_cons; apply/orP; left.
    by apply: IH=> c H3; apply: H; rewrite in_cons; apply/orP; right.
  Qed.      
  
  Lemma ln_big_product_sum (T : eqType) (cs : seq T) (f : T -> R) :
    (forall t : T, 0 < f t)%R -> 
    ln (big_product cs f) = big_sum cs (fun c => ln (f c)).
  Proof.
    elim: cs=> /=; first by rewrite ln_1.
    move=> a l IH H; rewrite ln_mult=> //; first by rewrite IH.
    by apply: big_product_gt0.
  Qed.    
    
  Lemma big_product_le (T : eqType) (cs : seq T) (f : T -> R) g :
    (forall c, c \in cs -> 0 <= f c)%R ->
    (forall c, c \in cs -> 0 <= g c)%R ->     
    (forall c, c \in cs -> f c <= g c)%R -> 
    (big_product cs f <= big_product cs g)%R.
  Proof.
    elim: cs=> //=.
    { move=> _ _ _; apply: Rle_refl. }
    move=> a l IH H1 H2 H3; apply Rmult_le_compat.
    { by apply: H1; rewrite in_cons; apply/orP; left. }
    { apply: big_product_ge0.
      by move=> c H4; apply: H1; rewrite in_cons; apply/orP; right. }
    { by apply: H3; rewrite in_cons; apply/orP; left. }
    apply: IH.
    { by move=> c H; apply: H1; rewrite in_cons; apply/orP; right. }
    { by move=> c H; apply: H2; rewrite in_cons; apply/orP; right. }
    by move=> c H; apply: H3; rewrite in_cons; apply/orP; right.
  Qed.    

  Lemma big_sum_le (T : eqType) (cs : seq T) (f : T -> R) g :
    (forall c, c \in cs -> f c <= g c)%R -> 
    (big_sum cs f <= big_sum cs g)%R.
  Proof.
    elim: cs=> //=.
    { move=> _; apply: Rle_refl. }
    move=> a l IH H1; apply Rplus_le_compat.
    { by apply: H1; rewrite in_cons; apply/orP; left. }
    by apply: IH=> c H; apply: H1; rewrite in_cons; apply/orP; right.
  Qed.    
  
  Lemma rat_to_R_prod T (cs : seq T) (f : T -> rat) :
    rat_to_R (\prod_(c <- cs) (f c)) =  
    big_product cs (fun c => (rat_to_R (f c)))%R.
  Proof.
    elim: cs=> //=; first by rewrite big_nil rat_to_R1.
    move=> a' l IH; rewrite big_cons.
    rewrite rat_to_R_mul IH.
    by f_equal; rewrite rat_to_R_plus rat_to_R_opp rat_to_R_mul.
  Qed.    
  
  Lemma rat_to_R_prod' (cs : seq costs) a :
    rat_to_R (\prod_(c <- cs) (1 - eps * c a)) =  
    big_product cs (fun c => (rat_to_R 1 - rat_to_R eps * rat_to_R (c a)))%R.
  Proof.
    rewrite rat_to_R_prod; apply: big_product_ext=> // x.
    by rewrite rat_to_R_plus rat_to_R_opp rat_to_R1 /Rminus rat_to_R_mul.
  Qed.    

  Lemma exprDr_seq (r : rat) (cs : seq costs) (a : A) :
    0 < r -> 
    Rpower (rat_to_R r) (rat_to_R (\sum_(c <- cs) c a)) =
    big_product cs (fun c => Rpower (rat_to_R r) (rat_to_R (c a))).
  Proof.
    move=> H; elim: cs=> //=.
    { rewrite big_nil rat_to_R0 Rpower_O=> //.
      have H2: (0 = rat_to_R 0)%R.
      { by rewrite /rat_to_R /Qreals.Q2R /= Rmult_0_l. }
      rewrite H2.
      by apply: rat_to_R_lt.
    }
    move=> a1 l IH; rewrite !big_cons.
    rewrite -IH.
    rewrite rat_to_R_plus.
    by rewrite Rpower_plus.
  Qed.

  Lemma neps_gt0 : 0 < 1 - eps.
  Proof.
    rewrite subr_gt0.
    have H3: (1/2%:R : rat) < 1.
    { by rewrite ltr_pdivr_mulr. }
    have H4: eps <= 1 / 2%:R.
    { by case: (andP eps_range). }
    by apply: (ler_lt_trans H4 H3).
  Qed.      
  
  Lemma neps_exp_le x y :
    Rle 0 x ->
    Rle x 1 ->
    Rlt 0 y ->
    Rle y (1/2) -> 
    Rle (Rpower (1 - y) x) (1 - y * x).
  Proof.
    move=> H H1 H2 H3; apply: neps_exp_le=> //.
    by split=> //; left.
  Qed.    

  Lemma rat_to_R_eps_gt0 : (0 < rat_to_R eps)%R.
  Proof.
    case: (andP eps_range)=> H1 H2.
    by rewrite -rat_to_R0; apply: rat_to_R_lt.
  Qed.

  Lemma rat_to_R_eps_pos : (0 <= rat_to_R eps)%R.
  Proof.
    by apply: Rlt_le; apply: rat_to_R_eps_gt0. 
  Qed.

  Lemma rat_to_R_eps_neq0 : (rat_to_R eps <> 0)%R.
  Proof.
    move=> H; move: rat_to_R_eps_gt0; rewrite H.
    apply: Rlt_irrefl.
  Qed.
  
  Lemma rat_to_R_eps_le_one_half : (rat_to_R eps <= 1/2)%R.
  Proof.
    case: (andP eps_range)=> H1 H2.
    have H3: (1 / 2 = rat_to_R (1 / 2%:R))%R.
    { rewrite /Rdiv rat_to_R_mul rat_to_R1; f_equal.
      by rewrite rat_to_R_inv rat_to_R2. }
    by rewrite H3; apply: rat_to_R_le.
  Qed.
  
  Lemma rat_to_R_neps : rat_to_R (1 - eps) = (1 - rat_to_R eps)%R.
  Proof. by rewrite rat_to_R_plus rat_to_R_opp rat_to_R1. Qed.

  Lemma rat_to_R_neps_gt0 : (0 < rat_to_R (1 - eps))%R.
  Proof. by rewrite -rat_to_R0; apply: rat_to_R_lt; apply: neps_gt0. Qed.
    
  Lemma Rpower_pos x y : (0 < x -> 0 <= y -> 0 < Rpower x y)%R.
  Proof.
    rewrite /Rpower.
    case: (Req_dec y 0%R).
    { move=> ->; rewrite Rmult_0_l exp_0.
      by move=> _ _; apply: Fourier_util.Rlt_zero_1. }
    move=> H H2 H3.
    apply: exp_pos.
  Qed.   

  Lemma one_minus_pos x : (x <= 1 -> 0 <= 1 - x)%R.
  Proof. move=> H; fourier. Qed.
  
  Definition pdist
             (cs : seq costs)
             (CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1)             
    : dist A [numDomainType of rat] :=
    mkDist (p_dist_axiom CMAX).

  (** The expected cost of the MW algorithm after [length cs] timesteps *)
  Definition expCost
             (cT : costs)
             (cs : seq costs)
             (CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1)
    : rat :=
    expectedValue (pdist CMAX) cT.
  
  (** The best fixed action wrt. cost functions [cs] *)
  Definition best_action (cs : seq costs) : A :=
    arg_min xpredT (fun a : A => \sum_(c <- cs) c a) a0.
  
  (** \Gamma^T >= (1 - \epsilon)^{OPT} *)
  Section OPT.
    Variable cT : costs.    
    Variable cs : seq costs.
    Notation cs' := ([:: cT & cs]).
    Variable CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1.
      
    Notation astar := (best_action cs).
    Notation OPT := (\sum_(c <- cs) c astar).
    Notation wT := (weights_of cs init_weights). 
    Notation gammaT := (gamma wT).
    Notation pT := (pdist CMAX).
    (** In expCostT, CMAX defines the distributed pT computed at time t. 
        cT is the cost function returned by the adversary, after pT has 
        been calculated. *)
    Notation expCostT := (expCost cT CMAX).
    
    Lemma gammaT_ge_wT_astar : wT astar <= gammaT.
    Proof.
      rewrite /gamma.
      apply: weight1_sum_ler=> a.
      apply/ltrW; apply: weights_of_gt0=> //.
      apply: init_weights_gt0.
    Qed.

    Lemma wT_astar_eq :
      rat_to_R (wT astar) =
      big_product cs (fun c => (rat_to_R 1 - rat_to_R eps * rat_to_R (c astar)))%R. 
    Proof. by rewrite weights_of_eq ffunE rat_to_R_prod'. Qed.

    Lemma rat_to_R_cost_pos a c : c \in cs -> (0 <= rat_to_R (c a))%R.
    Proof.
      rewrite -rat_to_R0=> H; case: (andP (CMAX H a))=> H2 H3.
      by apply: rat_to_R_le.
    Qed.

    Lemma rat_to_R_sumcost_pos a : (0 <= rat_to_R (\sum_(c <- cs) c a))%R.
    Proof.
      move: rat_to_R_cost_pos; elim: cs.
      { move=> _; rewrite big_nil rat_to_R0; apply: Rle_refl. }
      move=> c' l IH H; rewrite big_cons rat_to_R_plus.
      apply: Rplus_le_le_0_compat.
      by apply: H; apply/orP; left.
      by apply: IH=> a1 c H2; apply: H; apply/orP; right.
    Qed.        

    Lemma rat_to_R_cost_le1 a c : c \in cs -> (rat_to_R (c a) <= 1)%R.
    Proof.
      rewrite -rat_to_R1=> H; case: (andP (CMAX H a))=> H2 H3.
      by apply: rat_to_R_le.
    Qed.

    Lemma gammaT_ge_1eps_OPT :
      (Rpower (1 - rat_to_R eps) (rat_to_R OPT) <= rat_to_R gammaT)%R.
    Proof.
      have H: Rle (Rpower (rat_to_R 1 - rat_to_R eps) (rat_to_R OPT))
                  (rat_to_R (wT astar)).
      { rewrite wT_astar_eq.
        have H2:
          Rle (Rpower (rat_to_R 1 - rat_to_R eps) (rat_to_R (\sum_(c <- cs) c astar)))
              (big_product cs
                           (fun c : costs => Rpower (rat_to_R (1 - eps))
                                                    (rat_to_R (c astar))))%R.
        { rewrite -exprDr_seq; last by apply: neps_gt0.
          rewrite rat_to_R_plus rat_to_R_opp rat_to_R1.
          apply: Rle_Rpower_l; first by apply: rat_to_R_sumcost_pos.
          split.
          { by rewrite -rat_to_R_neps; apply: rat_to_R_neps_gt0. }
          by apply: Rle_refl. }
        apply: Rle_trans.
        apply: H2.
        apply: big_product_le.
        { move=> c H; apply: Rlt_le; apply: Rpower_pos.
          by apply: rat_to_R_neps_gt0.
          by apply: rat_to_R_cost_pos. }
        { move=> c H; rewrite rat_to_R1; apply: one_minus_pos.
          have H1: (rat_to_R eps <= 1)%R.
          { apply: Rle_trans; first by apply: rat_to_R_eps_le_one_half. fourier. }
          have H3: (rat_to_R (c astar) <= 1)%R.
          { by apply: rat_to_R_cost_le1. }
          have H4: (1 = 1 * 1)%R by rewrite Rmult_1_l.
          rewrite H4; apply: Rmult_le_compat=> //.
          apply rat_to_R_eps_pos.
          by apply: rat_to_R_cost_pos. }
        move=> c H3.
        rewrite rat_to_R1 rat_to_R_neps.
        case: (andP (CMAX H3 astar))=> H4 H5.
        apply: neps_exp_le.
        have H6: 0%R = rat_to_R 0 by rewrite rat_to_R0.
        by rewrite H6; apply: rat_to_R_le.
        have H6: 1%R = rat_to_R 1 by rewrite rat_to_R1.
        by rewrite H6; apply: rat_to_R_le.
        by apply: rat_to_R_eps_gt0.
        by apply rat_to_R_eps_le_one_half. }
      rewrite rat_to_R1 in H; apply: Rle_trans; first by apply: H.
      by apply: rat_to_R_le; apply: gammaT_ge_wT_astar.
    Qed.

    Lemma expCostT_eq :
      expCostT = \sum_(a : A) (wT a / gammaT) * cT a.
    Proof.
      rewrite /expCost /expectedValue /expectedCondValue /pT /p /= /p_aux.
      by apply: congr_big=> // i _; rewrite ffunE.
    Qed.        
    
    Lemma gammaT_Tprod1 :
      gamma (weights_of cs' init_weights) = gammaT * (1 - eps * expCostT).
    Proof.
      rewrite expCostT_eq.
      rewrite /weights_of -/weights_of /update_weights.
      rewrite /gamma sum_ffunE'.
      have H: \sum_t wT t * (1 - eps * cT t) =
              \sum_t (wT t - wT t * eps * cT t).
      { apply: congr_big=> // x _; rewrite mulrDr.
        by rewrite mulr1 -mulrA mulrN. }
      rewrite H sumrB.
      have H2: \sum_i wT i * eps * cT i =
               eps * \sum_i wT i * cT i.
      { have H3: \sum_i wT i * eps * cT i = \sum_i eps * (wT i * cT i).
        { by apply: congr_big=> // i _; rewrite mulrA [wT i * _]mulrC. }
        by rewrite H3 mulr_sumr. }
      rewrite H2.
      have H3: \sum_i wT i - eps * (\sum_i wT i * cT i) =
               gammaT * (1 - eps * (\sum_i wT i * cT i) / gammaT).
      { rewrite mulrDr mulr1 [(eps * _) / _]mulrC mulrN mulrA mulfV.
        { by rewrite mul1r. }
        by apply sum_weights_of_not0. }
      rewrite H3.
      rewrite /gammaT.
      f_equal.
      f_equal.
      f_equal.
      rewrite -mulrA; f_equal.
      rewrite mulr_suml; apply: congr_big=> // i _.
      by rewrite -mulrA [cT i / _]mulrC mulrA.
    Qed.
  End OPT.
 
  Lemma gamma0_sizeA : gamma init_weights = #|A|%:R.
  Proof.
    rewrite /gamma /init_weights sum_ffunE'.
    have H: \sum_(t : A) (1%:R : rat) = (\sum_(t : A) 1%N)%:R.
    { by rewrite natr_sum. }
    by rewrite H sum1_card.
  Qed.

  (** All nonempty subsequences of "cs" *)
  Fixpoint subSeqs_of A (cs : seq A) : seq (seq A) :=
    if cs is [:: c & cs'] then [:: cs & subSeqs_of cs']
    else [::].

  Lemma in_subSeqs_of (cs : seq costs) :
    cs != [::] -> cs \in subSeqs_of cs.
  Proof.
    case: cs; first by [].
    by move=> // a l H /=; rewrite in_cons; apply/orP; left.
  Qed.  
  
  Lemma subSeqs_of_CMAX (cs : seq costs)
        (CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1) :
    forall cs', cs' \in subSeqs_of cs ->
    forall c, c \in cs' -> forall a : A, 0 <= c a <= 1.
  Proof.
    elim: cs CMAX=> /=.
    { by move=> H cs'; rewrite in_nil. }
    move=> a l IH H cs'; rewrite in_cons; case/orP.
    { move/eqP=> -> c; rewrite in_cons; case/orP.
      { by move/eqP=> -> a1; apply: H; apply/orP; left. }
      by move=> H2; apply: H; apply/orP; right. }
    move=> H2 c H3.
    have H4: forall c, c \in l -> forall a, 0 <= c a <= 1.
    { by move=> c0 H4; apply: H; apply/orP; right. }
    by apply: (IH H4 cs' H2).
  Qed.    

  Lemma CMAX_nil :
    forall c : costs, c \in [::] -> forall a : A, 0 <= c a <= 1.
  Proof. by move=> c; rewrite in_nil. Qed.

  Definition CMAXb (cs : seq costs) :=
    all [pred c : costs | [forall a : A, 0 <= c a <= 1]] cs.

  Lemma CMAXb_behead (cs : seq costs) :
    CMAXb cs -> CMAXb (behead cs).
  Proof. by move/allP=> H; apply/allP=> y/mem_behead H2; apply: H. Qed.
  
  Lemma CMAXP (cs : seq costs) :
    reflect (forall c, c \in cs -> forall a : A, 0 <= c a <= 1) (CMAXb cs).
  Proof.
    case H: (CMAXb cs).
    { apply: ReflectT=> c H2 a; rewrite /CMAXb in H; move: (allP H).
      by move/(_ c)/(_ H2)=> /= => /forallP/(_ a). }
    apply: ReflectF=> H2; rewrite /CMAXb in H; move: (negbT H).
    move/allPn; case=> c H3; move/negP=> /=; apply; apply/forallP=> x.
    by apply: H2.
  Qed.    

  Lemma CMAXb_CMAX cs :
    CMAXb cs ->
    forall c, c \in cs -> forall a, 0 <= c a <= 1.
  Proof. by apply/CMAXP. Qed.
  
  Definition CMAX_costs_seq := {cs : seq costs | CMAXb cs}.
  
  Definition CMAX_seq (cs' : seq (seq costs)) := all CMAXb cs'.
  
  Program Fixpoint subSeqs_aux (cs' : seq (seq weights)) (CMAX : CMAX_seq cs')
    : seq CMAX_costs_seq
    := (match cs' as cs'' return _ = cs'' -> seq CMAX_costs_seq with
        | [::] => fun _ => [::]
        | [:: cs'' & cs'_rest] => fun pf => [:: exist _ cs'' _ & @subSeqs_aux cs'_rest _]
        end) erefl.
  Next Obligation. by case: (andP CMAX). Qed.
  Next Obligation. by case: (andP CMAX). Qed.
  
  Lemma CMAX_seq_subSeqs_of (cs : seq weights)
        (CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1)
    : CMAX_seq (subSeqs_of cs).
  Proof.
    elim: cs CMAX=> //= a l IH H; apply/andP; split.
    apply/andP; split.
    { by apply/forallP; apply: H; rewrite in_cons; apply/orP; left. }
    have H2: forall c, c \in l -> forall a, 0 <= c a <= 1.
    { by move=> c H2 a1; apply: H; rewrite in_cons; apply/orP; right. }
    case H0: (l == [::]).
    { move: (eqP H0)=> -> //. }
    { by apply: (allP (IH H2)); apply: in_subSeqs_of; rewrite H0. }
    by apply: IH=> c H2 a1; apply: H; rewrite in_cons; apply/orP; right.
  Qed.      
    
  Definition subSeqs (cs : seq weights)
             (CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1)
    : seq CMAX_costs_seq
    := @subSeqs_aux (subSeqs_of cs) (CMAX_seq_subSeqs_of CMAX). 
  
  Lemma gamma_prod_aux (cs : seq costs) c_bogus
        (CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1) :
    gamma (weights_of cs init_weights) =
    #|A|%:R * 
    \prod_(cs' <- @subSeqs cs CMAX)
     (1 - eps * @expCost (head c_bogus (projT1 cs'))
                         (behead (projT1 cs'))
                         (CMAXb_CMAX (CMAXb_behead (projT2 cs')))).
  Proof.
    elim: cs CMAX.
    { by move=> CMAX; rewrite /= big_nil mulr1 gamma0_sizeA. }
    move=> a l H CMAX; rewrite big_cons /=.
    rewrite gammaT_Tprod1.
    { by move=> c0 H2 a1; apply: CMAX; rewrite in_cons; apply/orP; right. }
    move=> pf0.
    rewrite H.
    rewrite -mulrA; f_equal.
    rewrite mulrC.
    move: (ssrfun.svalP _)=> pf1.
    move: (subSeqs_aux_obligation_2 _ _)=> pf2.
    move: (CMAXb_CMAX _)=> pf3.
    f_equal.
    rewrite /subSeqs.
    move: (CMAX_seq_subSeqs_of _)=> pf4.
    apply: congr_big=> //.
    f_equal.
    apply: proof_irrelevance.
  Qed.

  (** Some general lemmas about logarithms 
       -- should be moved elsewhere *)
  Lemma ln_le (x y : R) : (0 < x -> x <= y -> ln x <= ln y)%R.
  Proof.
    move=> H0; case=> H.
    left; apply: ln_increasing=> //.
    by right; subst x.
  Qed.

(* The construction of the derivability proof is needed to apply
    the compositional rules in the next two proofs *)
  Definition aux_const x : derivable_pt (fun x => (exp x - (1 +x))%R) x :=
    derivable_pt_minus exp (Rplus 1) x (derivable_pt_exp x)
      (derivable_pt_plus (fun _ : R => 1%R) id x (derivable_pt_const 1 x)
      (derivable_pt_id x)).

  Lemma aux_neg y (H :(y < 0)%R) :
    (derive (fun x => (exp x - (1 + x))%R) aux_const y < 0)%R.
  Proof.
    rewrite /derive /aux_const
            derive_pt_minus
            derive_pt_exp
            derive_pt_plus
            derive_pt_const
            derive_pt_id.
    apply Rlt_minus.
    rewrite -exp_0 Rplus_0_l.
    apply exp_increasing => //.
  Qed.

  Lemma aux_pos y (H :(0 <= y)%R) :
    (derive (fun x => (exp x - (1 + x))%R) aux_const y >= 0)%R.
  Proof.
    rewrite /derive /aux_const
            derive_pt_minus
            derive_pt_exp
            derive_pt_plus
            derive_pt_const
            derive_pt_id.
    apply Rge_minus.
    rewrite -exp_0 Rplus_0_l.
    apply Rle_ge.
    case: H => H;
    first by left; apply exp_increasing => //.
    right. f_equal => //.
  Qed.

  Lemma ln_Taylor_upper' x : ((1 + x) <= exp x)%R.
  Proof.
    clear A a0 eps eps_range.
    apply Rge_le.
    apply Rminus_ge.
    set f := fun x => (exp x - (1 + x))%R.
    have H0 : (f x = exp x - (1 + x))%R => //.
    rewrite -H0; clear H0.
    have H0 : (f 0 = 0)%R by
      rewrite /f exp_0 Rplus_0_r;
      apply Rminus_diag_eq => //.
    rewrite -H0.
    case: (Rtotal_order x 0) => H.
    {
      left.
      apply (MVT_cor1 f x 0 aux_const) in H.
      case: H => c; case => H1 H2.
      rewrite H0 !Rminus_0_l in H1.
      rewrite H0.
      have H3 :  (x < 0)%R
        by case: H2 =>  H2 H3; apply (Rlt_trans x c 0) => //.
      apply Ropp_eq_compat in H1.
      rewrite Ropp_involutive in H1.
      rewrite H1.
      apply Rlt_gt.
      rewrite Ropp_mult_distr_l.
      apply Rmult_lt_0_compat.
      apply Ropp_0_gt_lt_contravar.
      apply Rlt_gt.
      apply aux_neg.
      case: H2 => //.
      fourier.
    }
    {
      case: H => H;
      first by subst; rewrite /f Rplus_0_r exp_0; right => //.
      apply (MVT_cor1 f 0 x aux_const) in H.
      case: H => c; case => H1 H2.
      rewrite H0 !Rminus_0_r in H1.
      rewrite H0.
      have H3 :  (0 < x)%R
        by case: H2 =>  H2 H3; apply (Rlt_trans 0 c x) => //.
      rewrite H1.
      apply Rle_ge.
      rewrite -(Rmult_0_l x).
      apply Rmult_le_compat.
      right => //.
      left => //.
      apply Rge_le.
      apply aux_pos.
      left. case: H2 => //.
      right => //.
    }
  Qed.

  Lemma ln_Taylor_upper x : (x < 1)%R ->  (ln (1 - x) <= -x)%R.
  Proof.
    intros h.
    rewrite /ln.
    case_eq (Rlt_dec 0 (1-x)); move => h1 h2;
    last by apply False_rec; apply h1; fourier.
    rewrite /Rln => /=.
    destruct (ln_exists (1 - x) h1) as [x0 e0].
    apply Rplus_le_reg_l with (r := 1%R).
    rewrite /Rminus in e0.
    rewrite e0.
    apply ln_Taylor_upper'.
  Qed.

  Lemma deriv_aux_lower :
    derivable (fun x : R => ((1 - x) * exp (x + x ^ 2))%R).
  Proof.
    rewrite /derivable => x.
    apply derivable_pt_mult.
    apply derivable_pt_minus.
    apply derivable_pt_const.
    apply derivable_pt_id.
    set f1 := fun x => (x + x ^2)%R.
    set f2 := fun x => exp x.
    have H : (fun x0 : R => exp (x0 + x0 ^ 2))
              = Ranalysis1.comp f2 f1 => //.
    rewrite H.
    apply derivable_pt_comp.
    rewrite /f1.
    apply derivable_pt_plus.
    apply derivable_pt_id.
    apply derivable_pt_mult.
    apply derivable_pt_id.
    apply derivable_pt_mult.
    apply derivable_pt_id.
    apply derivable_pt_const.
    apply derivable_pt_exp.
  Defined.

  Lemma ln_Taylor_lower_aux_lt_0 x (H : (x < 0)%R) :
    (derive_pt (fun x : R => ((1 - x) * exp (x + x ^ 2))%R)
      x (deriv_aux_lower x) < 0)%R.
  Proof.
    rewrite /deriv_aux_lower
            derive_pt_mult
            derive_pt_minus
            derive_pt_const
            derive_pt_id
            (* Need to eliminate the substitution in the above proof *)
            /ssr_have /eq_rec_r /eq_rec /eq_rect => /=.
    rewrite derive_pt_comp
            derive_pt_exp
            derive_pt_plus
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_const.
    ring_simplify.
    set Y :=  exp (x + x * (x * 1)).
    have H0 : (- 2* Y * x ^ 2 + Y * x = Y * ( x * (-2 * x + 1)))%R
      by ring.
    rewrite H0.
    rewrite  -(Rmult_0_r Y).
    apply Rmult_lt_compat_l.
    apply exp_pos.
    rewrite  -(Rmult_0_r x).
    apply Rmult_lt_gt_compat_neg_l => //.
    fourier.
  Qed.

  Lemma ln_Taylor_lower_aux_gt_0
    x (H0 : (0 < x)%R) (H1 : (x  <= 1/2)%R) :
    (derive_pt (fun x : R => ((1 - x) * exp (x + x ^ 2))%R)
      x (deriv_aux_lower x) >= 0)%R.
  Proof.
    rewrite /deriv_aux_lower
            derive_pt_mult
            derive_pt_minus
            derive_pt_const
            derive_pt_id
            (* Need to eliminate the substitution in the above proof *)
            /ssr_have /eq_rec_r /eq_rec /eq_rect => /=.
    rewrite derive_pt_comp
            derive_pt_exp
            derive_pt_plus
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_const.
    ring_simplify.
    set Y :=  exp (x + x * (x * 1)).
    have H2 : (- 2* Y * x ^ 2 + Y * x = Y * ( x * (-2 * x + 1)))%R
      by ring.
    rewrite H2.
    rewrite  -(Rmult_0_r Y).
    apply Rmult_ge_compat_l.
    left.
    apply exp_pos.
    rewrite  -(Rmult_0_r x).
    apply Rmult_ge_compat_l => //. fourier.
    case: H1 => H1. fourier. subst. fourier.
  Qed.

  Lemma ln_Taylor_lower x : (x <= 1/2 -> -x - x^2 <= ln (1 - x))%R.
  Proof. 
    intros H.
    rewrite -[(-x - x^2)%R] ln_exp.
    apply ln_le; first by apply exp_pos.
    have h : ((- x - x ^2) = - (x + x^2))%R by field.
      rewrite h. clear h.
    apply (Rmult_le_reg_r (/exp (- (x + x ^ 2))));
      first by apply Rinv_0_lt_compat; apply exp_pos.
    rewrite Rinv_r;
      last by move: (exp_pos (- (x + x ^ 2))%R) => H0 H1; fourier.
    rewrite exp_Ropp Rinv_involutive;
      last by move: (exp_pos (x + x^2)%R) => H0 H1; fourier.
    set F := fun x => ((1 - x) * exp (x + x^2))%R.
    have H0 : (F x = (1 - x) * exp (x + x ^ 2))%R => //.
    rewrite -H0; clear H0.
    have H1 : (F 0 = 1)%R. rewrite /F.
    have H0 : (0 + 0^2 = 0)%R by ring.
      rewrite H0; ring_simplify; apply exp_0; clear H0.
    rewrite -H1.
    apply Rminus_le.
    case: (Rtotal_order 0 x) => H2; last case: H2 => H2.
    {
      move: (MVT_cor1 F 0 x deriv_aux_lower H2) => H3.
      destruct H3 as [c [H3 [H4 H5]]].
      have h : (F 0 - F x = - (F x - F 0))%R. ring.
      rewrite h H3. apply Rge_le. clear h.
      rewrite Rminus_0_r.
      apply Ropp_0_le_ge_contravar.
      apply Rmult_le_pos; last by fourier.
      apply Rge_le.
      apply ln_Taylor_lower_aux_gt_0 => //.
      fourier.
    }
    {
      right. subst. ring.
    }
    {
      move: (MVT_cor1 F x 0 deriv_aux_lower H2) => H3.
      destruct H3 as [c [H3 [H4 H5]]].
      rewrite H3.
      rewrite Rminus_0_l.
      rewrite -(Rmult_0_r (derive_pt F c (deriv_aux_lower c))%R).
      apply Rmult_le_compat_neg_l; last by fourier.
      left.
      apply ln_Taylor_lower_aux_lt_0 => //.
    }
  Qed.

  Lemma Rle_contra_tech x y z : (-x <= y + -z ->  z <= y + x)%R.
  Proof.
    have ->: (y + -z = -(-y + z))%R.
    { by rewrite Ropp_plus_distr Ropp_involutive. }
    move/Ropp_le_cancel/(Rplus_le_compat_r y).
    have ->: (-y + z + y = z)%R.
    { by rewrite Rplus_comm -Rplus_assoc Rplus_opp_r Rplus_0_l. }
    by rewrite Rplus_comm.
  Qed.    

  Lemma gamma_prod (cs : seq costs) c_bogus
        (CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1) :
    rat_to_R (gamma (weights_of cs init_weights)) =
    (rat_to_R #|A|%:R * 
     big_product
       (@subSeqs cs CMAX)
       (fun cs' => 
          (rat_to_R 1 -
           rat_to_R eps *
           rat_to_R (@expCost (head c_bogus (projT1 cs'))
                    (behead (projT1 cs'))
                    (CMAXb_CMAX (CMAXb_behead (projT2 cs')))))))%R.
  Proof.
    rewrite (gamma_prod_aux c_bogus CMAX) rat_to_R_mul; f_equal.
    rewrite rat_to_R_prod; apply: big_product_ext=> // x.
    by rewrite rat_to_R_plus rat_to_R_opp rat_to_R1 /Rminus rat_to_R_mul.
  Qed.

  (** OPT * ln(1 - \eps) <= ln n + \sum_[t=1,T] ln(1 - \eps * \nu^t) *)
  Section OPT2.
    Variable cT : costs.
    Variable cs : seq costs.
    Variable CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1.
    Variable cT_range : forall a, 0 <= cT a <= 1. 

    Notation astar := (best_action cs).
    Notation OPT := (\sum_(c <- cs) c astar).
    Notation OPTR := (rat_to_R OPT).
    Notation cs_subSeqs := (@subSeqs cs CMAX).
    Notation epsR := (rat_to_R eps).
    Notation size_A := (rat_to_R #|A|%:R).
    Notation expCostR cs :=
      (rat_to_R (expCost (head cT (projT1 cs))
                         (CMAXb_CMAX (CMAXb_behead (projT2 cs))))).
    
    Lemma expCostR_range 
          (c : sig_eqType
                 (T:=seq_eqType (finfun_of_eqType A rat_eqType))
                 CMAXb)
      : (0 <= expCostR c <= 1)%R.
    Proof.
      suff:
        0 <= (expCost (head cT (projT1 c))
                      (CMAXb_CMAX (CMAXb_behead (projT2 c)))) <= 1.
      { case/andP=> H1 H2; split.
        { rewrite -rat_to_R0; apply: rat_to_R_le=> //. }
        by rewrite -rat_to_R1; apply: rat_to_R_le. }
      apply: expectedValue_range=> x; case H: (projT1 c)=> //= [a l].
      move: (projT2 c); move/CMAXP/(_ a); rewrite /= H; apply.
      by rewrite in_cons; apply/orP; left.
    Qed.      

    Lemma epsR_lt1 : (epsR < 1)%R.
    Proof.
      apply: Rle_lt_trans; first by apply: rat_to_R_eps_le_one_half.
      fourier.
    Qed.

    Lemma epsR_expCostR_lt1
          (c : sig_eqType
                 (T:=seq_eqType (finfun_of_eqType A rat_eqType))
                 CMAXb)
      : (epsR * expCostR c < 1)%R.
    Proof.
      case: (Req_dec (expCostR c) 1)%R.
      { by move=> ->; rewrite Rmult_1_r; apply: epsR_lt1. }
      move=> H; case: (Req_dec (expCostR c) 0)%R.
      { move=> ->; rewrite Rmult_0_r; fourier. }
      move=> H2; rewrite -[1%R]Rmult_1_r; apply Rmult_gt_0_lt_compat.
      case: (expCostR_range c)=> H3 H4; apply: Rnot_le_gt=> H5.
      have H6: (expCostR c < 0)%R by case: H5.
      case: H3; first by move/Rlt_not_le.
      by move=> H7; rewrite -H7 in H2.
      fourier.
      apply: Rle_lt_trans; first by apply: rat_to_R_eps_le_one_half.
      fourier.
      by case: (expCostR_range c)=> _; case=> //.
    Qed.        
    
    Lemma neps_epsR_expCostR_gt0
          (c : sig_eqType
                 (T:=seq_eqType (finfun_of_eqType A rat_eqType))
                 CMAXb)
      : (0 < 1 - epsR * expCostR c)%R.
    Proof. apply: Rlt_Rminus; apply: epsR_expCostR_lt1. Qed.      
    
    Lemma neps_OPT_le_gamma_prod :
      (OPTR * ln (1 - epsR) <=
       ln size_A + big_sum cs_subSeqs (fun cs => ln (1 - epsR * expCostR cs)))%R.
    Proof.
      have H:
        (OPTR * ln (1 - epsR) = ln (Rpower (1 - epsR) OPTR))%R.
      { by rewrite ln_exp. }
      rewrite H -ln_big_product_sum.
      { rewrite -ln_mult.
        { apply: ln_le.
          { apply: Rpower_pos.
            by rewrite -rat_to_R_neps; apply: rat_to_R_neps_gt0.
            by apply: rat_to_R_sumcost_pos. }
          apply: Rle_trans; first by apply: gammaT_ge_1eps_OPT=> //.
          by rewrite (gamma_prod cT CMAX) rat_to_R1; apply: Rle_refl. }
        by apply: rat_to_R_Acard_gt0.
        by apply: big_product_gt0=> c H2; apply: neps_epsR_expCostR_gt0. }
      by move=> t; apply: neps_epsR_expCostR_gt0.
    Qed.

    Lemma OPT_neps2_le_gamma_sum :
      (OPTR * (-epsR - epsR^2) <=
       ln size_A + big_sum cs_subSeqs (fun cs => -epsR * expCostR cs))%R.
    Proof.
      apply: Rle_trans.
      apply: Rmult_le_compat_l.
      by apply: rat_to_R_sumcost_pos.
      apply: ln_Taylor_lower.
      by apply: rat_to_R_eps_le_one_half.
      apply: Rle_trans.
      apply: neps_OPT_le_gamma_prod.
      apply: Rplus_le_compat_l.
      apply: big_sum_le.
      move=> c H.
      rewrite -Ropp_mult_distr_l.      
      apply: ln_Taylor_upper; apply: epsR_expCostR_lt1.
    Qed.

    Lemma gamma_sum_le_OPT_1plus_eps :
      (big_sum cs_subSeqs (fun cs => expCostR cs) <=
       ln size_A / epsR + OPTR * (1 + epsR))%R.
    Proof.
      move: OPT_neps2_le_gamma_sum.
      rewrite /Rminus -Ropp_plus_distr Ropp_mult_distr_r_reverse.
      have H:
        (big_sum cs_subSeqs (fun cs0 : CMAX_costs_seq => - epsR * expCostR cs0) =
         big_sum cs_subSeqs (fun cs0 : CMAX_costs_seq => - (epsR * expCostR cs0)))%R.
      { apply: big_sum_ext=> // x.
        by rewrite Ropp_mult_distr_l_reverse. }
      rewrite H; move {H}.
      rewrite big_sum_nmul; move/Rle_contra_tech; rewrite big_sum_scalar.
      have H: (0 <= / epsR)%R.
      { rewrite -(Rmult_1_l (/ epsR)); apply: Rle_mult_inv_pos; first by fourier.
        by apply: rat_to_R_eps_gt0. }
      move/(Rmult_le_compat_l (/ epsR)); move/(_ H).
      rewrite -Rmult_assoc -(Rinv_l_sym epsR); last first.
      apply: rat_to_R_eps_neq0.
      rewrite Rmult_1_l=> H2; apply: Rle_trans; first by apply: H2.
      move {H H2}; have ->: (epsR + epsR^2 = epsR*(1 + epsR))%R.
      { rewrite Rmult_plus_distr_l Rmult_1_r.
        have ->: (2 = 2 * 1)%nat by [].
        by rewrite pow_sqr pow_1. }
      right; rewrite Rmult_plus_distr_l; f_equal.
      { by rewrite /Rdiv Rmult_comm. }
      rewrite -Rmult_assoc [(/ epsR * _)%R]Rmult_comm Rmult_assoc.
      rewrite -[(/epsR * _)%R]Rmult_assoc -Rinv_l_sym; first by rewrite Rmult_1_l.
      by apply: rat_to_R_eps_neq0.
    Qed.      

    Lemma OPTR_le_length_cs : (OPTR <= INR (length cs))%R.
    Proof.
      move: astar=> ax.
      elim: cs CMAX; first by rewrite /= big_nil rat_to_R0=> _; apply: Rle_refl.
      move=> a l /= IH; rewrite big_cons /= => H; rewrite rat_to_R_plus.
      have H2: (rat_to_R (a ax) <= 1)%R.
      { apply: (@rat_to_R_cost_le1 _ H ax a).
        by rewrite in_cons; apply/orP; left. }
      have H3: (rat_to_R (\sum_(c <- l) c ax) <= INR (length l))%R.
      { by apply: IH=> c H3 a1; apply: H; rewrite in_cons; apply/orP; right. }
      move {IH H}.
      suff: (rat_to_R (a ax) + rat_to_R (\sum_(j <- l) j ax) <= INR (length l) + 1)%R.
      move {H3}; case: l=> //=; rewrite Rplus_0_l; case=> H4; first by left.
        by right.
      by rewrite [(INR _ + _)%R]Rplus_comm; apply: Rplus_le_compat.
    Qed.      
    
    Lemma gamma_sum_le_OPT :
      (big_sum cs_subSeqs (fun cs => expCostR cs) <=
       OPTR + epsR * INR (length cs) + ln size_A / epsR)%R.
    Proof.
      apply: Rle_trans; first by apply: gamma_sum_le_OPT_1plus_eps.
      rewrite Rplus_comm.
      have H: (OPTR * (1 + epsR) + ln (size_A) / epsR <=
               OPTR + OPTR * epsR + ln (size_A) / epsR)%R.
      { by rewrite Rmult_plus_distr_l Rmult_1_r; apply: Rle_refl. }
      apply: Rle_trans; first by apply: H.
      rewrite [(_ + _ * INR (length cs))%R]Rplus_comm.
      rewrite [(_ + _ * epsR)%R]Rplus_comm.
      rewrite 2!Rplus_assoc; apply: Rplus_le_compat; last by apply: Rle_refl.
      { rewrite Rmult_comm.
        apply: Rmult_le_compat_l; last by apply: OPTR_le_length_cs.
        by apply: rat_to_R_eps_pos. }
    Qed.      
  End OPT2.
End weights.

Section weights_noregret.
  Local Open Scope ring_scope.

  Variable A : finType.   (** The strategy space *)
  Variable a0 a1 : A.     (** ... has size at least 2. *)
  Variable a01_distinct : a0 != a1.

  Lemma cardA_ge2 : (2 <= #|A|)%N.
  Proof.
    have H: (#|pred2 a0 a1| <= #|A|)%N.
    { by apply: subset_leq_card; apply/subsetP. }
    have H2: (1 < #|pred2 a0 a1|)%N by rewrite card2 a01_distinct.
    by apply: leq_trans; first by apply: H2.
  Qed.    
  
  Variable cs : seq (costs A).
  Variable CMAX : forall c, c \in cs -> forall a : A, 0 <= c a <= 1.
  Variable cs_size_gt0 : (0 < size cs)%N.

  (** [costs_default] remains unused assuming [size cs > 0]. *)
  Definition costs_default : costs A := finfun (fun _ => 1).
  Lemma costs_default_in_range : forall a : A, 0 <= costs_default a <= 1.
  Proof. by move=> a; rewrite /costs_default ffunE; apply/andP; split. Qed.
  
  Variable eps : rat.
  Variable eps_range : 0 < eps <= 1/2%:R.
  
  Notation astar := (best_action a0 cs).
  Notation OPT := (\sum_(c <- cs) c astar).
  Notation OPTR := (rat_to_R OPT).
  Notation cs_subSeqs := (@subSeqs _ cs CMAX).
  Notation epsR := (rat_to_R eps).
  Notation size_A := (rat_to_R #|A|%:R).
  Notation T := (INR (size cs)).

  Delimit Scope R_scope with R.

  Lemma T_gt0 : (0 < T)%R.
  Proof. by apply: lt_0_INR; move: cs_size_gt0; apply/ltP. Qed.

  Lemma Tinv_gt0 : (0 < / T)%R.
  Proof. by apply: Rinv_0_lt_compat; apply: T_gt0. Qed.

  (** The expected cost at time [T = size cs]. That is, the expected
      cost of [head cs] given the weights table computed from [behead cs]. *)
  Definition expCostR (cs : CMAX_costs_seq A) : R :=
    rat_to_R
      (expCost a0 eps_range
               (head costs_default (projT1 cs))
               (CMAXb_CMAX (CMAXb_behead (projT2 cs)))).
  
  (** Assuming [cs = [c_T; c_(T-1); ...; c_1]], 
      [expsCostsR] is the sum of 
        [expCostR [c_1] + expCostR [c_2; c_1] + ...
         expCostR [cT; ...; c2; c_1]]. *)
  Definition expCostsR : R :=
    (big_sum cs_subSeqs (fun cs0 => expCostR cs0))%R.
  
  Lemma weights_noregret :
    (expCostsR <= OPTR + epsR * T + (ln size_A / epsR))%R.
  Proof. by apply: gamma_sum_le_OPT; apply: costs_default_in_range. Qed.
  
  Lemma perstep_weights_noregret :
    ((expCostsR - OPTR) / T <= epsR + ln size_A / (epsR * T))%R.
  Proof.      
    have H0: (expCostsR - OPTR <= epsR * T + (ln size_A / epsR))%R.
    { have H1: (expCostsR - OPTR <= OPTR + epsR * T + (ln size_A / epsR) - OPTR)%R.
      { by rewrite /Rminus; apply: Rplus_le_compat_r; apply: weights_noregret. }
      apply: Rle_trans; first by apply: H1.
      rewrite /Rminus Rplus_comm Rplus_assoc -Rplus_assoc. 
      by rewrite [(- _ + _)%R]Rplus_comm Rplus_opp_r Rplus_0_l; apply: Rle_refl. }
    have H1: ((expCostsR - OPTR) / T <= (epsR * T + (ln size_A / epsR)) / T)%R.
    { rewrite /Rdiv; apply: Rmult_le_compat_r=> //.
      by apply: Rlt_le; apply: Tinv_gt0. }
    clear H0; apply: Rle_trans; first by apply: H1. clear H1.
    have H: ((epsR * T + ln size_A / epsR) / T = epsR + ln size_A / (epsR * T))%R.
    { rewrite Rdiv_plus_distr /Rdiv Rmult_assoc -Rinv_r_sym.
      rewrite Rmult_1_r Rmult_assoc Rinv_mult_distr=> //.
      by apply: rat_to_R_eps_neq0.
      by move: T_gt0=> H H2; rewrite H2 in H; apply Rlt_irrefl in H.
      by move: T_gt0=> H H2; rewrite H2 in H; apply Rlt_irrefl in H. }
    by rewrite H; clear H; apply: Rle_refl.
  Qed.
End weights_noregret.

  

