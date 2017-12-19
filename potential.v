Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import Num.Theory.

Require Import extrema games dynamics.

(** * Potential Games *)

Local Open Scope ring_scope.

Class PhiClass (pN : nat) (rty : realFieldType) (pT : finType)
      `(costAxiomClass : CostAxiomClass pN rty pT)
       (movesClass : MovesClass pN pT)
  : Type := Phi : state pN pT -> rty.

Class PhiAxiomClass (pN : nat) (rty : realFieldType) (pT : finType)
      `(costAxiomClass : CostAxiomClass pN rty pT)
       (movesClass : MovesClass pN pT)
       (phiClass : PhiClass costAxiomClass movesClass) : Type :=
  PhiAxiom : 
    forall (i : 'I_pN) (t : state pN pT) (t_i' : pT),
      moves i (t i) t_i' ->
      let t' := upd i t t_i' in 
      Phi t' - Phi t = cost i t' - cost i t.
Notation "'phi_ax'" := (@PhiAxiom _ _ _ _ _ _ _) (at level 50).

Class Potential (N : nat) (rty : realFieldType) (T : finType)
      `(costAxiomClass : CostAxiomClass N rty T)
      (movesClass : MovesClass N T)
      (phiClass : PhiClass costAxiomClass movesClass)
      (phiAxiomClass : PhiAxiomClass phiClass)
  : Type := {}.

Section PotentialLemmas.
  Context `{potentialClass : Potential}.
  Notation sT := (state N T).
  
  Definition minimal : pred sT :=
    [pred t : sT | [forall t' : sT, Phi t <= Phi t']].

  Lemma Phi_cost_le (t : sT) i (t_i' : T) :
    moves i (t i) t_i' ->
    let t' := upd i t t_i' in 
    Phi t <= Phi t' -> cost i t <= cost i t'.
  Proof.
    move=> Hmoves t'.
    rewrite -subr_ge0=> H0.
    generalize (phi_ax Hmoves)=> H2. 
    by rewrite -subr_ge0 -H2.
  Qed.      

  Lemma cost_Phi_lt (t : sT) i t_i' :
    moves i (t i) t_i' ->
    let t' := upd i t t_i' in     
    cost i t' < cost i t -> Phi t' < Phi t.
  Proof.
    move=> Hmoves.
    generalize (phi_ax Hmoves)=> H0 t'.
    by rewrite -subr_lt0 -H0 subr_lt0.
  Qed.        
  
  (** Any [t] minimal wrt. the potential function [Phi] is 
      a Pure Nash Equilibrium. *)
  Lemma minimal_PNE (t : sT) : minimal t -> PNE t.
  Proof.
    rewrite /minimal=> /=; move/forallP=> H0 i.
    by move=> t_i' Hmoves; move: H0; move/(_ (upd i t t_i')); apply: Phi_cost_le.
  Qed.

  Definition Phi_minimizer (t0 : sT) : sT := arg_min predT Phi t0.

  Lemma minimal_Phi_minimizer (t0 : sT) : minimal (Phi_minimizer t0).
  Proof.
    have H0: predT t0 by [].
    by case: (andP (arg_minP Phi H0)).
  Qed.  

  Lemma PNE_Phi_minimizer (t0 : sT) : PNE (Phi_minimizer t0).
  Proof.
    apply: minimal_PNE.
    apply: minimal_Phi_minimizer.
  Qed.    
  
  (** Assuming [T] is inhabited, every potential game over [T] has at
      least one PNE. *)
  Lemma exists_PNE (t0 : sT) : exists t : sT, PNE t.
  Proof.
    exists (Phi_minimizer t0).
    apply: PNE_Phi_minimizer.
  Qed.    
End PotentialLemmas.

Section BestResponseDynamics.
  Context `{potentialClass : Potential}.
  Notation sT := (state N T).
  
  Inductive step : sT -> sT -> Prop :=
  | step_progress (t : sT) (i : 'I_N) t_i' :
      moves i (t i) t_i' ->
      let t' := upd i t t_i' in 
      cost i t' < cost i t -> step t t'.
      
  Definition halted (t : sT) := PNE t.

  Let hstate := (simpl_pred sT * simpl_pred sT * sT)%type.
  
  Definition P (sut : hstate) : Prop :=
    let: (s,u,t) := sut in
    forall t0, s t0 -> Phi t <= Phi t0.

  Lemma init_P t : P (init t).
  Proof. by move=> t0 /=; move/eqP=> <-. Qed.
  
  Lemma step_P s u t t' :
    inv (s,u,t) -> P (s,u,t) -> step t t' -> 
    [/\ u t' & P (predU1 t' s, predD1 u t', t')].
  Proof.
    case=> H0 H1 H2 H3; inversion 1; subst.
    rename H5 into Hmoves.
    rename H6 into H5.
    rename t'0 into t'.
    have Hx: Phi t' < Phi t.
    { subst t'.
      by apply: (cost_Phi_lt Hmoves).
    }
    suff: ~~ s t'; last first.
    { apply/negP; move=> H6.
      move: (H3 _ H6)=> H7.
      move: (ltrW Hx)=> H8'.
      have H9: Phi t' <> Phi t.
      { apply/eqP.
        by rewrite ltr_eqF.
      }
      move: H7 H9; rewrite !ler_eqVlt; case/orP; first by move/eqP=> <-.
      move => H9 H10.
      have H11: Phi t' < Phi t'.
      { apply: ler_lt_trans.
        apply: H8'.
        apply: H9.
      }
      by rewrite ltrr in H11.
    }
    move=> H6.
    move: (H3 t')=> /=.
    move: (H0 t')=> /=.
    case: (s t') H6=> //= _.
    rewrite (mem_enum sT _).
    move=> He _; split.
    { by rewrite He. }
    move=> t0; case/orP; first by move/eqP=> <-.
    move=> H6.
    apply: ltrW.
    apply: ltr_le_trans.
    subst t'.
    apply: Hx.
    apply: (H3 t0 H6).
  Qed.    

  Lemma halted_doesnt_step t t' :
    halted t -> step t t' -> False.
  Proof.
    rewrite /halted=> H0; inversion 1; subst.
    move: (H0 i)=> H4.
    rename t'0 into t'.
    generalize (ltr_le_asym (cost i t') (cost i t)).
    by subst t'; rewrite H3 H4.
  Qed.    

  Lemma better_response_safe t : 
    safe step halted t.
  Proof.    
    move=> t''; induction 1=> //.
    case: (PNEP t).
    { by move=> H0; right.
    }
    move=> H0; left.
    suff H2: ~~ (@PNEb _ _ _ H movesClass t); last first.
    { apply/negP=> H1; case: (PNE_PNEb t)=> H2 H3.
      by apply: H0; apply H3.
    }
    rewrite negb_forall in H2; case: (existsP H2)=> i; rewrite negb_forall.
    case/existsP=> t'; rewrite negb_imply; case/andP=> H3; move/negP=> H4.
    exists (upd i t t'); apply: (step_progress (i:=i))=> //.
    by rewrite ltrNge; apply/negP.
  Qed.
  
  Lemma better_response_everywhere_halts t :
    everywhere_halts step halted t.
  Proof.
    apply: (step_everywhere_halts_or_stuck P).
    apply: init_P.
    apply: step_P.
    apply: halted_doesnt_step.
    apply: better_response_safe.
  Qed.    
End BestResponseDynamics.

Print Assumptions better_response_everywhere_halts.

Section PriceOfStabilityBound.
  (** The following section proves a bound on the Price of Stability 
      of potential games. *)
  Context `{potentialClass : Potential}.
  Notation sT := (state N T).
  
  (** We assume the social cost function is positive. *)
  Hypothesis Cost_pos : forall t : sT, 0 < Cost t.
  
  (** The bound [A] must also be positive; otherwise, dividing by [A] 
      in [AB_bound_Phi] is undefined. *)
  Variables A B : rty.
  Hypothesis (HAgt0 : 0 < A).

  (** The bound is proved assuming there exist real numbers [A] and [B] 
      such that for any state [t], [Phi t] is bounded on the left by 
      [Cost t / A] and bounded on the right by [B * Cost t]. *)
  Hypothesis AB_bound_Phi :
    forall t : sT, Cost t / A <= Phi t <= B * Cost t.

  (** Under the conditions stated above, the Price of Stability of 
      any potential game is at most [A * B]. (For games in which the 
      PNE is unique, this bound gives a bound on the Price of Anarchy
      as well.) *)
  Lemma POS_bounded (t0 : sT) (PNE_t0 : PNE t0) : POS t0 t0 <= A * B.
  Proof.
    set (tN := Phi_minimizer t0).
    generalize (minimal_Phi_minimizer t0); move/forallP=> HtN.
    case: (andP (AB_bound_Phi tN))=> H3 H4; rewrite /POS.
    set (tStar := arg_min predT Cost t0).
    move: (HtN tStar)=> H5.
    case: (andP (AB_bound_Phi tStar))=> H6 H7.
    rewrite ler_pdivr_mulr; last by apply: Cost_pos.
    apply: ler_trans.
    have H8: Cost (arg_min PNEb Cost t0) <= Cost tN.
    { have H9: PNE tN by apply: PNE_Phi_minimizer.
      have H10: PNEb t0 by move: PNE_t0; case: (PNEP t0).
      case: (andP (arg_minP Cost H10)).
      by move=> H11; move/forallP; move/(_ tN)/implyP; apply; rewrite -PNE_PNEb.
    }
    apply: H8.
    rewrite ler_pdivr_mulr in H3=> //.
    have H8: Phi tN * A <= Phi tStar * A.
    { rewrite GRing.mulrC [Phi tStar * _]GRing.mulrC.
      apply: ler_mull=> //.
      by apply/ltrW.
    }
    apply: ler_trans; [apply: H3|].
    apply: ler_trans; [apply: H8|].
    rewrite GRing.mulrC -GRing.mulrA.
    by apply: ler_mull; first by apply: ltrW.
  Qed.
End PriceOfStabilityBound.
