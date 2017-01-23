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
    forall i : 'I_N, moves i (t i) (t' i).
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
      \sum_(i : 'I_sN) cost i (upd i t (t' i)) <=
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
    have H2: Cost t <= \sum_i cost i (upd i t (t' i)).
    { rewrite /Cost; apply: ler_sum=> /= i _; rewrite /PNE in Hpne.
      by apply: Hpne.
    }
    by apply: ler_trans; [apply: H2|]; apply: smooth_ax.
  Qed.

  Lemma smooth_PNE (t t' : (T ^ N)%type) :
    PNE t ->
    valid_Move t t' ->
    Cost t <= (lambda of T / (1 - mu of T)) * Cost t'.
  Proof.
    move=> Hpne Hval.
    move: (smooth_PNE_aux Hpne Hval).
    rewrite addrC -ler_subl_addl.
    have H3: Cost t - mu of T * Cost t = (1 - mu of T) * (Cost t).
    { by rewrite -{1}[Cost t]mul1r -mulrBl.
    }
    rewrite H3 mulrC -ler_pdivl_mulr; last first.
    { move: mu_lt1.
      by rewrite ltr_subr_addr addrC addr0.
    }
    by rewrite -mulrA [(1 - _)^-1 * _]mulrC mulrA.
  Qed.

  Lemma smooth_PNE_POA (t0 t1 : state N T) :
    PNE t0 ->
    optimal t1 ->
    valid_Move (T:=T) (arg_max PNEb Cost t0) (arg_min optimal Cost t1) ->
    0 < Cost (arg_min optimal Cost t1) -> 
    POA t0 t1 <= lambda of T / (1 - mu of T).
  Proof.
    move/PNEP => Ht0 Hopt Hval Hpos.
    have Hpne: PNE (arg_max PNEb Cost t0).
    { by case: (andP (arg_maxP Cost Ht0)); move/PNEP. }
    move: (smooth_PNE (t':=arg_min optimal Cost t1) Hpne Hval) => H2.
    by rewrite -ler_pdivr_mulr in H2.
  Qed.
  
  Definition dist_valid_Move
             (d : dist [finType of state N T] rty)
             (t' : state N T) :=
    forall t : {ffun 'I_N -> T}, t \in support d -> valid_Move t t'.
  
  Lemma smooth_CCE_aux (d : dist [finType of state N T] rty) (t' : state N T) :
    CCE d ->
    dist_valid_Move d t' -> 
    ExpectedCost d <= lambda of T * Cost t' + mu of T * ExpectedCost d.
  Proof.
    move=> Hcce Hval.
    have H2: ExpectedCost d
          <= \sum_(i : 'I_N) expectedUnilateralCost i d (t' i).
    { apply: ler_sum=> /= i _.
      apply: (CCE_elim Hcce)=> t_i X.
      by apply: Hval.
    }
    apply: ler_trans; [apply: H2|].
    rewrite (expectedUnilateralCost_linear d t').
    have H3:
      expectedValue d
        (fun t : {ffun 'I_N -> T} =>
           \sum_(i < N) cost i (upd i t (t' i)))
    <= expectedValue d
        (fun t : state N T => lambda of T * Cost t' + mu of T * Cost t).
    { rewrite expectedValue_linear expectedValue_const /expectedValue.
      have H3: \sum_t d t * (\sum_(i < N) cost i ((upd i t) (t' i)))
            <= expectedValue d (fun t => lambda of T * Cost t' + mu of T * Cost t).
      { apply: ler_sum=> t _.
        case Hgt0: (0 < d t).
        { apply: ler_mull=> //; apply: smooth_ax.
          apply: Hval => //.
          by apply/supportP.
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
    CCE d -> 
    dist_valid_Move d t' ->
    ExpectedCost d <= (lambda of T / (1 - mu of T)) * Cost t'.
  Proof.
    move=> Hcce Hval.
    move: (smooth_CCE_aux Hcce Hval).
    rewrite addrC -ler_subl_addl.
    have H3: ExpectedCost d - mu of T * ExpectedCost d = (1 - mu of T) * (ExpectedCost d).
    { by rewrite -{1}[ExpectedCost d]mul1r -mulrBl.
    }
    rewrite H3 mulrC -ler_pdivl_mulr; last first.
    { move: mu_lt1.
      by rewrite ltr_subr_addr addrC addr0.
    }
    by rewrite -mulrA [(1 - _)^-1 * _]mulrC mulrA.
  Qed.
End SmoothLemmas.

Print Assumptions smooth_CCE.
