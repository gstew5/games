Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema dist games dynamics potential.

(** (\lambda,\mu)-Smooth Games

    See, e.g., 
    https://www.math.uwaterloo.ca/~cswamy/courses/co759/agt-material/
      robust-roughgarden.pdf *)

Local Open Scope ring_scope.

Section ValidMove.
  Context T `{gameClass : game T}.
  
  Definition valid_Move (t t' : (T ^ N)%type) :=
    forall i : 'I_N, Move i t (upd i t t').
End ValidMove.

Class LambdaClass (lT : finType) (rty : realFieldType)
  : Type := lambda_val : rty.
Notation "'lambda' 'of' T" := (@lambda_val T _ _) (at level 30).

Instance finCloneLambdaInstance lT rty `(H : LambdaClass lT rty) :
  @LambdaClass [finType of lT] rty :=
  @lambda_val _ _ H.

Class LambdaAxiomClass (lT : finType) (rty : realFieldType)
      `(LambdaClass lT rty)
  : Type := lambda_axiom : 0 <= lambda of lT.

Class MuClass (mT : finType) (rty : realFieldType) 
  : Type := mu_val : rty.
Notation "'mu' 'of' T" := (@mu_val T _ _) (at level 30).

Instance finCloneMuInstance lT rty `(H : MuClass lT rty) :
  @MuClass [finType of lT] rty :=
  @mu_val _ _ H.

Class MuAxiomClass (mT : finType) (rty : realFieldType)
      `(MuClass mT rty)
  : Type := mu_axiom : 0 <= mu of mT < 1.

Class SmoothnessAxiomClass (sT : finType) (sN : nat) (rty : realFieldType)
      `(costAxiomInstance : CostAxiomClass sN rty sT)
      (movesInstance : MovesClass sN sT)
      (gameInstance : game costAxiomInstance movesInstance)
      `(lambdaAxiomInstance : LambdaAxiomClass sT rty)
      `(muAxiomInstance : MuAxiomClass sT rty) : Type :=
  SmoothnessAxiom :
    forall t t' : (sT ^ sN)%type,
      valid_Move t t' -> 
      \sum_(i : 'I_sN) cost i (upd i t t') <=
      lambda of sT * Cost t' + mu of sT * Cost t.
Notation "'smooth_ax'" := (@SmoothnessAxiom _ _ _ _ _ _ _ _).

Class smooth (T : finType) (N : nat) (rty : realFieldType)
      `(costAxiomInstance : CostAxiomClass N rty T)
      (movesInstance : MovesClass N T)
      (gameInstance : game costAxiomInstance movesInstance)
      `(lambdaAxiomInstance : LambdaAxiomClass T rty)
      `(muAxiomInstance : MuAxiomClass T rty)
      (smoothnessAxiomInstance :
         SmoothnessAxiomClass gameInstance lambdaAxiomInstance muAxiomInstance)
  : Type := {}.

(*************************)
(** Negative cost smooth *)

Class NegativeMuAxiomClass
      `(MuClass) : Type :=
  negative_mu_axiom : mu of mT <= 0.

Class NegativeCostSmoothnessAxiomClass
      (cT : finType) (cN : nat) (rty : realFieldType)
      `(negativeGameInstance :
          negative_cost_game cT cN rty)
      `(lambdaAxiomInstance : LambdaAxiomClass cT rty)
      `(negativeMuAxiomInstance : NegativeMuAxiomClass cT rty) : Type :=
  NegativeCostSmoothnessAxiom :
    forall t t' : (cT ^ cN)%type,
      valid_Move t t' -> 
      \sum_(i : 'I_cN) cost i (upd i t t') <=
      lambda of cT * Cost t' + mu of cT * Cost t.
Notation "'negative_cost_smooth_ax'" := (@NegativeCostSmoothnessAxiom _ _ _ _ _ _ _ _ _ _ _ _).

Class negative_cost_smooth
      `(negativeCostSmoothnessAxiomInstance :
          NegativeCostSmoothnessAxiomClass)
  : Type := {}.

(** End negative cost smooth *)
(*****************************)

(******************)
(** Payoff smooth *)

Class PayoffMuAxiomClass
      (mT : finType)
      `(MuClass mT) : Type :=
  payoff_mu_axiom : 0 <= mu of mT.

Class PayoffSmoothnessAxiomClass
      (cT : finType) (cN : nat) (rty : realFieldType)
      `(gameInstance : payoff_game cT cN rty)
      `(lambdaAxiomInstance : LambdaAxiomClass cT rty)
      `(payoffMuAxiomInstance : PayoffMuAxiomClass cT rty) : Type :=
  PayoffSmoothnessAxiom :
    forall t t' : (cT ^ cN)%type,
      valid_Move t t' ->
      \sum_(i : 'I_cN) payoff i (upd i t t') >=
      lambda of cT * Payoff t' - mu of cT * Payoff t.
Notation "'payoff_smooth_ax'" := (@PayoffSmoothnessAxiom _ _ _ _ _ _ _ _ _ _ _ _).

Class payoff_smooth
      `(payoffsmoothnessAxiomInstance : PayoffSmoothnessAxiomClass)
  : Type := {}.

(** End payoff smooth *)
(**********************)

(******************************************)
(** Payoff smooth -> negative cost smooth *)

(** NOTE: This instance must have priority lower than that of 
    finCloneMuInstance. For now, I've given it the (rather low)
    priority 99 (0 is highest). An alternative solution is to 
    make the cost_of_payoff instance stack type-directed. -GS *)
Instance negativeCostMuInstance_of_payoffMuInstance
         (T : finType) (rty : realFieldType)
         (payoffMuInstance : MuClass T rty)
  : MuClass T rty | 99 :=
  - payoffMuInstance.

Instance negativeCostMuAxiomInstance_of_payoffMuAxiomInstance
         (mT : finType) (rty : realFieldType)
         `(payoffMuAxiomInstance : PayoffMuAxiomClass mT rty)
  : NegativeMuAxiomClass (negativeCostMuInstance_of_payoffMuInstance _).
Proof.
  rewrite /PayoffMuAxiomClass /mu_val in payoffMuAxiomInstance.
  rewrite /NegativeMuAxiomClass /negativeCostMuInstance_of_payoffMuInstance
          /mu_val.
  move: payoffMuAxiomInstance. move => PMAI.
    by rewrite oppr_le0.
Qed.

Lemma sum_opp N (rty : realFieldType) (T : finType)
      (f : 'I_N -> {ffun 'I_N -> T} -> rty)
      (t : {ffun 'I_N -> T}) :
  \sum_(i < N) - f i t = \sum_(i < N) (-1%:R : rty) * f i t.
Proof. apply: congr_big => //. move => i _. by rewrite mulN1r. Qed.

Lemma sum_opp_D N (rty : realFieldType) (T : finType)
      (f : 'I_N -> {ffun 'I_N -> T} -> rty)
      (t : {ffun 'I_N -> T}) :
  \sum_(i < N) - f i t = - \sum_(i < N) f i t.
Proof. by rewrite sum_opp -big_distrr /= mulN1r. Qed.

Lemma sum_opp_upd N (rty : realFieldType) (T : finType)
      (f : 'I_N -> {ffun 'I_N -> T} -> rty)
      (t t' : {ffun 'I_N -> T}) :
  \sum_(i < N) - f i [ffun j => if i == j then t' j else t j] =
  \sum_(i < N) (-1%:R : rty) * f i [ffun j => if i == j then t' j else t j].
Proof. apply: congr_big => //. move => i _. by rewrite mulN1r. Qed.

Lemma sum_opp_D_upd N (rty : realFieldType) (T : finType)
      (f : 'I_N -> {ffun 'I_N -> T} -> rty)
      (t t' : {ffun 'I_N -> T}) :
  \sum_(i < N) - f i [ffun j => if i == j then t' j else t j] =
  - \sum_(i < N) f i [ffun j => if i == j then t' j else t j].
Proof. by rewrite sum_opp_upd -big_distrr /= mulN1r. Qed.

Instance negativeCostSmoothnessAxiomInstance_of_payoffSmoothnessAxiomInstance
         `(payoffSmoothnessAxiomInstance : PayoffSmoothnessAxiomClass)
  : NegativeCostSmoothnessAxiomClass     
      (negative_cost_game_of_payoff_game _ _ _ _) _
      (negativeCostMuAxiomInstance_of_payoffMuAxiomInstance _ _ _).
Proof.
  rewrite /PayoffSmoothnessAxiomClass /mu_val in payoffSmoothnessAxiomInstance.
  rewrite /NegativeCostSmoothnessAxiomClass /Cost /cost_fun
          /negativeCostInstance_of_payoffInstance.
  rewrite /mu_val /negativeCostMuInstance_of_payoffMuInstance.
  move => t0 t' Hvm.
  rewrite 2!sum_opp_D sum_opp_D_upd ler_oppl mulrNN opprD mulrN opprK.
  apply: payoffSmoothnessAxiomInstance => //.
Qed.

Instance negative_cost_smooth_of_payoff_smooth
         `(p_smooth : payoff_smooth)
  : negative_cost_smooth _
  :=
    (Build_negative_cost_smooth
       (negativeCostSmoothnessAxiomInstance_of_payoffSmoothnessAxiomInstance
          _)
    ).

(** End Payoff smooth -> negative cost smooth *)
(**********************************************)

Section SmoothLemmas.
  Context {T : finType}.
  Context `{smoothClass : smooth T}.

  Lemma lambda_pos : 0 <= lambda of T.
  Proof. apply: lambda_axiom. Qed.

  Lemma mu_pos : 0 <= mu of T.
  Proof. by case: (andP (@mu_axiom _ _ _ muAxiomInstance)). Qed.
  
  Lemma mu_lt1 : mu of T < 1.
  Proof. by case: (andP (@mu_axiom _ _ _ muAxiomInstance)). Qed.
  
  Lemma smooth_PNE_aux (t t' : (T ^ N)%type) :
    PNE t ->
    valid_Move t t' -> 
    Cost t <= lambda of T * Cost t' + mu of T * Cost t.
  Proof.
    move=> Hpne Hval.
    have H2: Cost t <= \sum_i cost i (upd i t t').
    { rewrite /Cost; apply: ler_sum=> /= i _; rewrite /PNE in Hpne.
      by apply: (Hpne _ (upd i t t') (Hval i)).
    }
    by apply: ler_trans; [apply: H2|]; apply: smooth_ax.
  Qed.

  Lemma smooth_PNE (t t' : (T ^ N)%type) :
    mu of T < 1 -> 
    PNE t ->
    valid_Move t t' ->
    Cost t <= (lambda of T / (1 - mu of T)) * Cost t'.
  Proof.
    move=> Hlt1 Hpne Hval.
    move: (smooth_PNE_aux Hpne Hval).
    rewrite addrC -ler_subl_addl.
    have H3: Cost t - mu of T * Cost t = (1 - mu of T) * (Cost t).
    { by rewrite -{1}[Cost t]mul1r -mulrBl.
    }
    rewrite H3 mulrC -ler_pdivl_mulr; last first.
    { by rewrite ltr_subr_addr addrC addr0.
    }
    by rewrite -mulrA [(1 - _)^-1 * _]mulrC mulrA.
  Qed.

  Definition dist_valid_Move
             (d : dist [finType of state N T] rty)
             (t' : state N T) :=
    forall i : 'I_N,
    forall t : {ffun 'I_N -> T},
      0 < d t -> Move i t ((upd i t) t').
  
  Lemma smooth_CCE_aux (d : dist [finType of state N T] rty) (t' : state N T) :
    CCE d ->
    optimal t' ->
    dist_valid_Move d t' -> 
    ExpectedCost d <= lambda of T * Cost t' + mu of T * ExpectedCost d.
  Proof.
    move=> Hcce Hopt Hval.
    have H2: ExpectedCost d
          <= \sum_(i : 'I_N) expectedUnilateralCost i d t'.
    { apply: ler_sum=> /= i _.
      by apply: (CCE_elim Hcce)=> ? X; apply: Hval; apply: in_support.
    }
    apply: ler_trans; [apply: H2|].
    rewrite expectedUnilateralCost_linear.
    have H3:
      expectedValue d
        (fun t : {ffun 'I_N -> T} =>
           \sum_(i < N) cost i (upd i t t'))
    <= expectedValue d
        (fun t : state N T => lambda of T * Cost t' + mu of T * Cost t).
    { rewrite expectedValue_linear expectedValue_const /expectedValue.
      have H3: \sum_t d t * (\sum_(i < N) cost i ((upd i t) t'))
            <= expectedValue d (fun t => lambda of T * Cost t' + mu of T * Cost t).
      { apply: ler_sum=> t _.
        case Hgt0: (0 < d t).
        { apply: ler_mull=> //; apply: smooth_ax.
          by move=> i; apply: (Hval i t Hgt0).
        }
        have H3: d t = 0.
        { move: (dist_positive d t)=> Hpos; rewrite ltr_def in Hgt0.
          move: Hgt0; rewrite Hpos andbC /=; case Heq: (d t == 0)=> //= _.
          by apply: (eqP Heq).
        }
        by rewrite H3 2!mul0r.
      }
      apply: ler_trans; first by apply: H3.
      by rewrite expectedValue_linear expectedValue_const /expectedValue.
    }
    apply: ler_trans; first by apply: H3.
    have H4:
      expectedValue d
        (fun t : {ffun 'I_N -> T} => lambda of T * Cost t' + mu of T * Cost t)
    = lambda of T * Cost t' +
      expectedValue d
        (fun t : {ffun 'I_N -> T} => mu of T * Cost t).
    { by rewrite expectedValue_linear expectedValue_const.
    }
    by rewrite H4 ExpectedCost_linear expectedValue_mull.
  Qed.

  Lemma smooth_CCE (d : dist [finType of state N T] rty) (t' : state N T) :
    mu of T < 1 -> 
    CCE d -> 
    optimal t' ->
    dist_valid_Move d t' ->
    ExpectedCost d <= (lambda of T / (1 - mu of T)) * Cost t'.
  Proof.
    move=> Hlt1 Hcce Hopt Hval.
    move: (smooth_CCE_aux Hcce Hopt Hval).
    rewrite addrC -ler_subl_addl.
    have H3: ExpectedCost d - mu of T * ExpectedCost d = (1 - mu of T) * (ExpectedCost d).
    { by rewrite -{1}[ExpectedCost d]mul1r -mulrBl.
    }
    rewrite H3 mulrC -ler_pdivl_mulr; last first.
    { by rewrite ltr_subr_addr addrC addr0.
    }
    by rewrite -mulrA [(1 - _)^-1 * _]mulrC mulrA.
  Qed.
End SmoothLemmas.

Print Assumptions smooth_CCE.
