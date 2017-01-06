Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema dist.
Require Import games smooth christodoulou.

Local Open Scope ring_scope.

(** This module defines combinators over multiplayer games. *)

(** A generic wrapper for directing the construction of cost games
    over finite types [T]. [I] is a phantom type, used to direct
    instance resolution. *)
Inductive Wrapper (I : eqType) (T : finType) : Type :=
  Wrap : T -> Wrapper I T.
Definition unwrap (I : eqType) (T : finType) (w : Wrapper I T) : T :=
  match w with Wrap t => t end.

Section Wrapper.
  Variable I : eqType.
  Variable T : finType.
Definition Wrapper_eq (t1 t2 : Wrapper I T) :=
  match t1, t2 with
  | Wrap t1', Wrap t2' => t1'==t2'
  end.                                 
Lemma Wrapper_eqP : Equality.axiom Wrapper_eq.
Proof.
  case=> s; case=> t /=; case H: (s == t).
  by move: (eqP H)=> ->; constructor.
  by constructor; case => e; subst s; rewrite eq_refl in H.
Qed.    
Definition Wrapper_eqMixin := EqMixin Wrapper_eqP.
Canonical Wrapper_eqType := Eval hnf in EqType (Wrapper I T) Wrapper_eqMixin.

Definition T_of_Wrapper (w : Wrapper I T) : T := unwrap w.
Definition Wrapper_of_T (t : T) : Wrapper I T := Wrap _ t.
Lemma T_of_WrapperK : cancel T_of_Wrapper Wrapper_of_T.
Proof. by case. Qed.
Definition Wrapper_choiceMixin := CanChoiceMixin T_of_WrapperK.
Canonical Wrapper_choiceType :=
  Eval hnf in ChoiceType (Wrapper I T) Wrapper_choiceMixin.
Definition Wrapper_countMixin := CanCountMixin T_of_WrapperK.
Canonical Wrapper_countType :=
  Eval hnf in CountType (Wrapper I T) Wrapper_countMixin.

Definition Wrapper_enum := map (fun x => Wrap I x) (Finite.enum T).
Lemma Wrapper_enumP : Finite.axiom Wrapper_enum.
Proof. by rewrite /Wrapper_enum; case => s; rewrite count_map; apply/enumP. Qed.

Definition unwrap_ffun (N : nat) (t : (Wrapper I T)^N) : T^N :=
  finfun (fun i => unwrap (t i)).
End Wrapper.

Definition Wrapper_finMixin (I : eqType) (T : finType) :=
  Eval hnf in FinMixin (@Wrapper_enumP I T).
Canonical Wrapper_finType (I : eqType) (T : finType) :=
  Eval hnf in FinType (Wrapper I T) (Wrapper_finMixin I T).

(** A generic Moves instance for Wrapper types; this may be overrided
    below for specific wrapped types. *)
Instance WrapperMovesInstance
         (I : eqType) (T : finType) (N : nat)
         `(MovesClass N T)
  : MovesClass N [finType of Wrapper I T] :=
  fun (i : 'I_N) =>
    [rel s t : Wrapper I T | moves i (unwrap s) (unwrap t)].

Section WrapperLemmas.
  Variables (I : eqType) (T : finType) (N : nat).
  Context `(MovesClass N T).
  
  Lemma valid_Move_wrap (t t' : (Wrapper I T)^N) :
    valid_Move (unwrap_ffun t) (unwrap_ffun t') ->
    valid_Move t t'.    
  Proof.
    rewrite /valid_Move => H2 i; case: (andP (H2 i)) => H3 H4.
    rewrite /Move; apply/andP; split.
    rewrite /(moves) /WrapperMovesInstance/=.
    by move: H3; rewrite /upd /unwrap_ffun /unwrap !ffunE eq_refl.
    apply/forallP => x; move: (forallP H4); move/(_ x)/implyP => H5.
    apply/implyP => H6; move: (H5 H6); rewrite /upd /unwrap_ffun !ffunE.
    by rewrite /unwrap; case: (t x) => s; case: (i == x) => //; case: (t' x).
  Qed.

  Lemma valid_Move_unwrap (t t' : (Wrapper I T)^N) :
    valid_Move t t' ->        
    valid_Move (unwrap_ffun t) (unwrap_ffun t').
  Proof.
    rewrite /valid_Move => H2 i; case: (andP (H2 i)) => H3 H4.
    rewrite /Move; apply/andP; split.
    rewrite /(moves) /WrapperMovesInstance/=.
    by move: H3; rewrite /upd /unwrap_ffun /unwrap !ffunE eq_refl.
    apply/forallP => x; move: (forallP H4); move/(_ x)/implyP => H5.
    apply/implyP => H6; move: (H5 H6); rewrite /upd /unwrap_ffun !ffunE.
    by rewrite /unwrap; case: (t x) => s; case: (i == x) => //; case: (t' x).
  Qed.

  Lemma valid_Move_unwrapP (t t' : (Wrapper I T)^N) :
    valid_Move t t' <->
    valid_Move (unwrap_ffun t) (unwrap_ffun t').
  Proof.
    split; first by apply: valid_Move_unwrap.
    by apply valid_Move_wrap.
  Qed.

  Context `(game T N).
  
  Lemma unwrap_ffun_simpl (t t' : (Wrapper I T)^N) :
    \sum_(i < N)
     (cost) i [ffun i0 => unwrap ([ffun j => if i == j then t' j else t j] i0)] =
    \sum_(i < N)
     (cost) i [ffun j => if i == j then unwrap (t' j) else unwrap (t j)].
  Proof.
    apply/congr_big=> // i _; f_equal; apply/ffunP => j; rewrite !ffunE.
    by case: (i == j).
  Qed.

  Lemma unwrap_eta (t t' : (Wrapper I T)^N) :
    \sum_(i < N) (cost) i [ffun j => if i == j then unwrap (t' j) else unwrap (t j)] =
    \sum_(i < N)
     (cost) i [ffun j => if i == j
                         then [ffun i0 => unwrap (t' i0)] j
                         else [ffun i0 => unwrap (t i0)] j].
  Proof. by apply/congr_big=> // i _; f_equal; apply/ffunP => j; rewrite !ffunE. Qed.
End WrapperLemmas.

(** Resource Games *)

Inductive resource : Type :=
| RYes : resource
| RNo : resource.

Definition resource_eq (r1 r2 : resource) :=
  if r1 is RYes then if r2 is RYes then true else false
  else if r2 is RYes then false else true.
Lemma resource_eqP : Equality.axiom resource_eq.
Proof. by case; case; try constructor. Qed.
Definition resource_eqMixin := EqMixin resource_eqP.
Canonical resource_eqType := Eval hnf in EqType resource resource_eqMixin.

Definition bool_of_resource (r : resource) : bool :=
  if r is RYes then true else false.
Definition resource_of_bool (b : bool) : resource :=
  if b then RYes else RNo.
Lemma bool_of_resourceK : cancel bool_of_resource resource_of_bool.
Proof. by case. Qed.
Definition resource_choiceMixin := CanChoiceMixin bool_of_resourceK.
Canonical resource_choiceType :=
  Eval hnf in ChoiceType resource resource_choiceMixin.
Definition resource_countMixin := CanCountMixin bool_of_resourceK.
Canonical resource_countType :=
  Eval hnf in CountType resource resource_countMixin.

Definition resource_enum := [:: RYes; RNo].
Lemma resource_enumP : Finite.axiom resource_enum.
Proof. by case. Qed.
Definition resource_finMixin := Eval hnf in FinMixin resource_enumP.
Canonical resource_finType := Eval hnf in FinType resource resource_finMixin.

Section resourceDefs.
  Context (N : nat) (rty : realFieldType).
  Local Open Scope ring_scope.

  Definition traffic (f : {ffun 'I_N -> resource}) := #|RNo.-support f|.

  Definition traffic' (f : {ffun 'I_N -> resource}) :=
    (\sum_(i < N | f i == RYes) 1)%N.

  Lemma pred_no_yes (f : {ffun 'I_N -> resource}) :
    (#|[pred x | f x != RNo]| = #|[pred x | f x == RYes]|)%N.
  Proof.
    apply: eq_card=> x; rewrite /in_mem /=.
    case H3: (f x)=> //.
  Qed.    
  
  Lemma trafficP f : traffic f = traffic' f.
  Proof.
    rewrite /traffic /traffic'.
    by rewrite /support_for sum1_card pred_no_yes.
  Qed.        

  Lemma traffic_pos f : (0 : rty) <= (traffic f)%:R.
  Proof.
    rewrite /traffic; case H: #|RNo.-support f|=> //.
    by apply: ler0n.
  Qed.
  
  Definition resourceCostFun (i : 'I_N) (f : {ffun 'I_N -> resource}) : rty :=
    if f i is RYes then (traffic f)%:R else 0.
End resourceDefs.

Instance resourceCostInstance (N : nat)
  : CostClass N rat_realFieldType [finType of resource] :=
  fun (i : 'I_N) (f : {ffun 'I_N -> resource}) =>
    resourceCostFun rat_realFieldType i f.

Program Instance resourceCostAxiomInstance (N : nat)
  : @CostAxiomClass N rat_realFieldType [finType of resource] _.
Next Obligation.
  rewrite /cost_fun /resourceCostInstance /resourceCostFun.
  case: (f i)=> //. apply: traffic_pos.
Qed.

Instance resourceMovesInstance
         (N : nat)
  : MovesClass N [finType of resource] :=
  fun (i : 'I_N) => [rel r r' : resource | true].

Instance resourceGame (N : nat) : @game [finType of resource] N _ _ _ _.

Instance resourceLambdaInstance 
  : LambdaClass [finType of resource] rat_realFieldType| 0 := 5%:R/3%:R.

Program Instance resourceLambdaAxiomInstance
  : @LambdaAxiomClass [finType of resource] rat_realFieldType _.

Instance resourceMuInstance
  : MuClass [finType of resource] rat_realFieldType | 0 := 1%:R/3%:R.

Instance resourceMuAxiomInstance
  : @MuAxiomClass [finType of resource] rat_realFieldType _.
Proof. by []. Qed.

Lemma Cost_traffic_sq N t:
  \sum_(i < N) cost i t = (traffic t)%:R ^+ 2.
Proof.
  have ->: ((traffic t)%:R ^+ 2 = (traffic t)%:R * (traffic t)%:R) by [].
  rewrite {2} trafficP.
  rewrite /cost_fun /resourceCostInstance /resourceCostFun.
  rewrite /traffic' -natrM big_distrr /=.
  have ->: ((\sum_(i < N | t i == RYes) traffic (N:=N) t * 1)%:R =
            \sum_(i < N | t i == RYes) (traffic (N:=N) t)%:R * 1).
  { move => t0. rewrite mulr1 muln1. rewrite natr_sum => //. }
  have ->: (\sum_(i < N | t i == RYes) (traffic (N:=N) t)%:R * 1 =
            \sum_(i < N | t i == RYes) (traffic (N:=N) t)%:R).
  { move => t0. apply congr_big => //. move => i H. rewrite mulr1 => //. }
  have ->: (\sum_(i < N | t i == RYes) (traffic (N:=N) t)%:R =
            (\sum_(i < N) if t i == RYes then (traffic (N:=N) t)%:Q else 0)).
  { by rewrite -big_mkcond. }
    by apply congr_big => //; move => i H; case: (t i).
Qed.

Lemma traffic_1_pos N t :
  0 <= (traffic (N:=N) t)%:Q + 1.
Proof. apply: addr_ge0 => //. apply: traffic_pos. Qed.

Lemma sum_one_term N i t t':
  (\sum_(i0 < N)
    (if ((if i == i0 then t' i0 else t i0) == RYes)
          && (i0 == i) then 1 else 0))%N =
  (if t' i == RYes then 1 else 0)%N.
Proof. by rewrite -big_mkcond big_mkcondl big_pred1_eq eq_refl. Qed.

(* each mixed term can be at most (traffic t) + 1
   (1 more than the unmixed cost) and there are exactly
   (traffic t') such terms (when t' i = RNo, the term is 0) *)
Lemma Cost_mixed_le N t t' :
  \sum_(i < N) cost i (upd i t t') <=
  (traffic t')%:R * ((traffic t)%:R + 1).
Proof.
  have H0: (forall i, cost i (upd i t t') <= (traffic t)%:R + 1).
  { move => i.
    rewrite /cost_fun /resourceCostInstance /resourceCostFun /=.
    rewrite ffunE eq_refl.
    case t'i: (t' i).
    - rewrite /traffic /support_for.
      rewrite (cardD1x (j:=i)).
      suff: (#|[pred i0 | t i0 != RNo & i0 != i]|
             <= #|[pred x | t x  != RNo]|)%N.
      { have <-: #|[pred i0 | t i0 != RNo & i0 != i]|
        = #|[pred i0 |
             [ffun j => if i == j then t' j else t j] i0 != RNo & i0 != i]|.
        { apply: eq_card=> x; rewrite /in_mem /= ffunE.
          case H: (x == i)=> /=; first by rewrite 2!andbF.
          rewrite 2!andbT; case H2: (i == x)=> //.
          move: (eqP H2)=> H3; rewrite H3 /= eq_refl in H; congruence. }
        rewrite addrC natrD=> H; apply: ler_add=> //.
          by rewrite ler_nat; apply: H. }
      apply: subset_leq_card.
        by apply/subsetP=> x; rewrite /in_mem /=; case/andP.
        rewrite ffunE eq_refl; apply/eqP=> H; rewrite H in t'i; congruence.
    - apply: traffic_1_pos.
  }
  have H: \sum_(i < N) (cost) i ((upd i t) t') <=
          (\sum_(i < N | t' i == RYes) (cost) i ((upd i t) t') : rat).
  { have ->: (\sum_(i < N | t' i == RYes) (cost) i ((upd i t) t') =
              \sum_(i < N) if t' i == RYes then (cost) i ((upd i t) t') else 0)
      by rewrite -big_mkcond.
    rewrite /cost_fun /resourceCostInstance /resourceCostFun.
    rewrite ler_eqVlt. apply /orP. left. apply /eqP.
    apply congr_big => //.
    move => i _. simpl. rewrite ffunE. rewrite eq_refl.
    case: (t' i) => //.
  }
  apply: ler_trans.
  apply: H.
  move {H}.
  have H: \sum_(i < N | t' i == RYes) (cost) i ((upd i t) t') <=
          \sum_(i < N | t' i == RYes) ((traffic (N:=N) t)%:R + 1).
  { apply: ler_sum.
    move => i H.
    rewrite /cost_fun /resourceCostInstance /resourceCostFun.
    rewrite /upd ffunE eq_refl 2!trafficP /traffic'.
    move: H; move => /eqP H; rewrite H.
    have ->: ((\sum_(i0 < N |
                     [ffun j => if i == j then t' j else t j] i0 == RYes) 1)%N =
              ((\sum_(i0 < N |
                      ([ffun j => if i == j then t' j else t j] i0 == RYes)
                        && (i0 == i)) 1)%N +
               (\sum_(i0 < N |
                      ([ffun j => if i == j then t' j else t j] i0 == RYes)
                        && (i0 != i)) 1)%N)%N).
    { by rewrite -bigID. }
    rewrite natrD addrC. apply: ler_add.
    have ->: (\sum_(i0 < N |
                    ([ffun j => if i == j then t' j else t j] i0 == RYes)
                      && (i0 != i)) 1)%N =
    (\sum_(i0 < N) if ((if i == i0 then t' i0 else t i0) == RYes)
                        && (i0 != i) then 1 else 0)%N.
    { by rewrite big_mkcond /=;apply congr_big => //;move => i0 _;rewrite ffunE. }
    have ->: ((\sum_(i0 < N | t i0 == RYes) 1)%N =
              (\sum_(i0 < N) if t i0 == RYes then 1 else 0)%N).
    { by rewrite big_mkcond. }
    rewrite ler_nat. apply leq_sum. move => i0 _.
    case i_i0: (i == i0).
    - have ->: ((i0 != i) = false).
      { by rewrite eq_sym; apply /negPf; rewrite i_i0. }
      rewrite andbF.
      case: (t i0 == RYes) => //.
    - have ->: ((i0 != i) = true).
      { rewrite eq_sym. apply (introT (P := i != i0)). apply: idP.
        apply (contraFneq (b := false)). move => H'. rewrite -i_i0  H'.
        apply: eq_refl => //. by []. }
      rewrite andbT => //.
      have ->: ((\sum_(i0 < N |
                       ([ffun j => if i == j then t' j else t j] i0 == RYes)
                         && (i0 == i)) 1)%N =
                (\sum_(i0 < N) if (((if i == i0 then t' i0 else t i0) == RYes)
                                     && (i0 == i)) then 1 else 0)%N).
      { by rewrite big_mkcond;apply: congr_big => //;move => i0 _;rewrite ffunE. }
      rewrite sum_one_term. case: (t' i) => //.
  }
  apply: ler_trans; first by apply: H.
  move {H}.
  have ->: \sum_(i < N | t' i == RYes) ((traffic (N:=N) t)%:R + 1) =
  (\sum_(i < N | t' i == RYes) 1 * ((traffic (N:=N) t)%:R + 1) : rat).
  { by apply: congr_big=> // i _; rewrite mul1r. }
  rewrite -mulr_suml. apply: ler_wpmul2r. apply: traffic_1_pos.
  have ->: \sum_(i | t' i == RYes) 1 =
  (\sum_(i | t' i == RYes) 1)%N%:R.
  { by move => t0; rewrite natr_sum. } (*%:R = GRing.natmul*)
  rewrite sum1_card /traffic /support_for /SimplPred /=.
  have <-: #|[pred x | t' x != RNo]| = #|[pred x | t' x == RYes]|.
  { by apply: pred_no_yes. }
    by [].
Qed.

Lemma resourceSmoothnessAxiom N (t t' : (resource ^ N)%type) :
  valid_Move t t' ->
  \sum_(i : 'I_N) cost i (upd i t t') <=
  lambda of [finType of resource] * Cost t' +
  mu of [finType of resource] * Cost t.
Proof.
  move=> _; rewrite /Cost.
  rewrite /lambda_val /resourceLambdaInstance.
  rewrite /mu_val /resourceMuInstance.
  have H0: (\sum_(i < N) (cost) i ((upd i t) t') <=
            (traffic t')%:R * ((traffic t)%:R + 1)).
  { by apply: Cost_mixed_le. }
  have H1: ((traffic (N:=N) t')%:R * ((traffic (N:=N) t)%:R + 1) <=
            5%:R / 3%:R * (\sum_i (cost) i t') +
            1%:R / 3%:R * (\sum_i (cost) i t)).
  { by rewrite !Cost_traffic_sq; apply: Christodoulou.result. }
  apply: ler_trans H0 H1.
Qed.

Program Instance resourceSmoothAxiomInstance N
  : @SmoothnessAxiomClass [finType of resource] N rat_realFieldType _ _ _ _ _ _ _ _.
Next Obligation. by apply: resourceSmoothnessAxiom. Qed.

Instance resourceSmoothInstance N
  : @smooth [finType of resource] N rat_realFieldType _ _ _ _ _ _ _ _ _.

(** Location Games *)

Inductive location (T : finType) : Type :=
  Location : forall l : {set T}, location T.

Definition location_eq T (l1 l2 : location T) :=
  match l1, l2 with
  | Location x1, Location x2 => x1 == x2
  end.
Lemma location_eqP T : Equality.axiom (@location_eq T).
Proof.
  case => x1; case => x2 /=; case H: (x1 == x2); constructor.
  by move: (eqP H) => ->.
  by case=> H2; rewrite H2 eq_refl in H.
Qed.    
Definition location_eqMixin T := EqMixin (@location_eqP T).
Canonical location_eqType T := Eval hnf in EqType (location T) (@location_eqMixin T).

Definition set_of_location T (l : location T) : {set T} :=
  match l with Location x => x end.
Definition location_of_set (T : finType) (x : {set T}) : location T := Location x.
Lemma set_of_locationK T : cancel (@set_of_location T) (@location_of_set T).
Proof. by case. Qed.
Definition location_choiceMixin T := CanChoiceMixin (@set_of_locationK T).
Canonical location_choiceType T :=
  Eval hnf in ChoiceType (location T) (@location_choiceMixin T).
Definition location_countMixin T := CanCountMixin (@set_of_locationK T).
Canonical location_countType T :=
  Eval hnf in CountType (@location T) (@location_countMixin T).

Lemma Location_inj T : injective (Location (T:=T)).
Proof. by move=> x y; case=> ->. Qed.

Definition location_enum (T : finType) := map (@Location T) (enum {set T}).
Lemma location_enumP T : Finite.axiom (location_enum T).
Proof.
  move=> x; apply: Finite.uniq_enumP.
  { rewrite map_inj_uniq; first by apply: enum_uniq.
    by apply: Location_inj. }
  move=> y; rewrite /location_enum inE; case: y => l; rewrite mem_map.
  by rewrite mem_enum.
  by apply: Location_inj.    
Qed.  
  
Definition location_finMixin T := Eval hnf in FinMixin (@location_enumP T).
Canonical location_finType T := Eval hnf in FinType (location T) (@location_finMixin T).

Section locationDefs.
  Context (N : nat) (rty : realFieldType) (T : finType).
  Context `{game [finType of {set T}] N rty}.
  Variable C : {set T} -> rty.
  Local Open Scope ring_scope.

  Definition U (s : {ffun 'I_N -> {set T}}) : {set T} :=
    [set l | [exists i, l \in s i]].
  
  Definition submodular (f : {set T} -> {set T}) :=
    forall s t : {set T},
      s \subset t ->
      C (s :&: t) + C (s :|: t) >= C s + C t.

  Definition W s := (C (U s)).

  Definition nullify_player (i : 'I_N) (s : {ffun 'I_N -> {set T}}) :=
    finfun (fun j => if i == j then set0 else s j).

  Definition Z i (s s' : {ffun 'I_N -> {set T}}) :=
    U s :|: \bigcup_(j : 'I_N | (j <= i)%N) (s j).
  
  Variable C_cond1 :
    forall (i : 'I_N) s, cost i s <= W s - W (nullify_player i s).
  Variable C_cond2 : forall s, \sum_(i : 'I_N) cost i s >= W s.
  Variable C_antimono :
    forall s t : {set T}, s \subset t -> C s >= C t.

  Lemma location_lem1 s s' :
    \sum_(i : 'I_N) cost i (upd i s s') <= W s' - W s.
  Proof.
    have H1:
      \sum_(i < N) (cost) i ((upd i s) s') <=
      \sum_(i < N) (W (upd i s s') - W (nullify_player i s)).
    { admit. }
    apply: ler_trans; first by apply: H1.
    have H2:
      \sum_(i < N) (W ((upd i s) s') - W (nullify_player i s)) <=
      \sum_(i < N) (C (Z i s s') - C (Z (i - 1) s s')).
    { admit. }
    apply: ler_trans; first by apply: H2.
    rewrite big_split /W => /=.
    have ->:
      \sum_(i < N) - C (Z (i - 1) s s') =
      - \sum_(i < N) C (Z (i - 1) s s').
    { admit. }
    have H3: \sum_(i < N) C (Z i s s') <= C (U s').
    { admit. }
    have H4: C (U s) <= \sum_(i < N) C (Z (i - 1) s s').
    { admit. }
    apply: ler_add => //; by rewrite ler_oppl opprK.
  Admitted.             
End locationDefs.

(** "Boolable" Types *)

Class Boolable (A : Type) : Type :=
  boolify : A -> bool.

Instance boolable_Resource : Boolable resource :=
  fun r => match r with RYes => true | RNo => false end.

(** Singleton Games A : Boolable, 
    c_i s = if (boolify s_i) then 1 else 0 *)

Section SingletonType.
Variable rty : realFieldType.
  
Inductive Singleton : Type := mkSingleton : Singleton.

Definition Singleton_eq (s1 s2 : Singleton) : bool := true.

Lemma Singleton_eqP : Equality.axiom Singleton_eq.
Proof. by case; case; constructor. Qed.
  
Definition Singleton_eqMixin := EqMixin Singleton_eqP.
Canonical Singleton_eqType := Eval hnf in EqType Singleton Singleton_eqMixin.

Definition singleton (A : finType) :=
  Wrapper [eqType of Singleton] A.

Definition singletonType (A : finType) :=
  [finType of Wrapper [eqType of Singleton] A].
End SingletonType.

Instance BoolableSingleton (A : finType) `(Boolable A)
  : Boolable (singletonType A) :=
  fun (s : singletonType A) => boolify (unwrap s).

Instance singletonCostInstance
         (N : nat) (rty : realFieldType) (A : finType)
         `(costA : CostClass N rty A)
         `(boolableA : Boolable A)
  : CostClass N rty (singletonType A) :=
  fun (i : 'I_N) (f : {ffun 'I_N -> singletonType A}) =>
    if boolify (f i) then 1 else 0.

Program Instance  singletonCostAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(costA : CostAxiomClass N rty A)
        `(boolableA : Boolable A)        
  : @CostAxiomClass
      N rty
      (singletonType A)
      (@singletonCostInstance N rty _ _ _).
Next Obligation.
  rewrite /(cost) /singletonCostInstance; case: (boolify _); first by apply: ler01.
  by apply: lerr.
Qed.

(*Uses the generic move instance for wrapped types*)

Instance singletonGameInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(Boolable A) 
        `(gameA : game A N rty)
  : @game (singletonType A) N rty _ _ _.

Module SingletonGameTest. Section singletonGameTest.
  Context {A N rty} `{gameA : game A N rty} `{Boolable A}.
  Variables (t : {ffun 'I_N -> singletonType A}) (i : 'I_N).
  Check cost i t.
End singletonGameTest. End SingletonGameTest.

Instance singletonLambdaInstance
         (rty : realFieldType) (A : finType)
         `(lambdaA : LambdaClass A rty)
  : @LambdaClass (singletonType A) rty | 0 := lambda of A.

Program Instance singletonLambdaAxiomInstance
        (rty : realFieldType) (A : finType)
        `(lambdaA : LambdaAxiomClass A rty)
  : @LambdaAxiomClass (singletonType A) rty _ | 0.

Instance singletonMuInstance
         (rty : realFieldType) (A : finType)
         `(lambdaA : MuClass A rty)
  : @MuClass (singletonType A) rty | 0 := mu of A.

Program Instance singletonMuAxiomInstance
        (rty : realFieldType) (A : finType)
        `(lambdaA : MuAxiomClass A rty)
  : @MuAxiomClass (singletonType A) rty _ | 0.

Class LambdaGe1Class (A : finType) N (rty : realFieldType) `(smooth A N rty)
  : Type := lambda_ge1 : 1 <= lambda of A.

Program Instance singletonSmoothAxiomInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{boolableA : Boolable A}
         `{LambdaGe1Class A N rty}
  : @SmoothnessAxiomClass (singletonType A) N rty _ _ _ _ _ _ _ _.
Next Obligation.
  rewrite /Cost /(cost) /singletonCostInstance.
  rewrite /lambda_val /singletonLambdaInstance.
  rewrite /mu_val /singletonMuInstance.
  have ->:
   \sum_(i < N)
      (if boolify ([ffun j => if i == j then t' j else t j] i) then 1 else 0) =
   \sum_(i < N) (if boolify (t' i) then 1 else (0 : rty)).
  { by apply/congr_big => // i _; rewrite ffunE eq_refl. }
  rewrite -[\sum_i (if boolify (t' i) then 1 else 0)]addr0; apply: ler_add.
  rewrite addr0; apply: ler_pemull=> //.
  apply: sumr_ge0 => // i _; case: (boolify _) => //; apply: ler01.
  apply: mulr_ge0; first by apply: mu_pos.
  by apply: sumr_ge0 => // i _; case: (boolify _) => //; apply: ler01.
Qed.  

Instance singletonSmoothInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{boolableA : Boolable A}
         `{LambdaGe1Class A N rty}
  : @smooth (singletonType A) N rty _ _ _ _ _ _ _ _ _.

Module SingletonSmoothTest. Section singletonSmoothTest.
  Context {A N rty} `{gameA : smooth A N rty}.
  Context `{Boolable A} `{LambdaGe1Class A N rty}.
  Lemma x0 (t : {ffun 'I_N -> (singletonType A)}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> (singletonType A)}) (i : 'I_N) :
    cost i t == lambda of (singletonType A). Abort.
End singletonSmoothTest. End SingletonSmoothTest.

(** Product Games A * B *)

Instance prodCostInstance
         (N : nat) (rty : realFieldType) (aT bT : finType)
         `(costA : CostClass N rty aT)
         `(costB : CostClass N rty bT)         
  : CostClass N rty [finType of (aT*bT)] :=
  fun (i : 'I_N) (f : {ffun 'I_N -> aT*bT}) =>
    cost i (finfun (fun j => (f j).1)) +
    cost i (finfun (fun j => (f j).2)).  

Program Instance  prodCostAxiomInstance
         (N : nat) (rty : realFieldType) (aT bT : finType)
         `(costA : CostAxiomClass N rty aT)
         `(costB : CostAxiomClass N rty bT)         
  : @CostAxiomClass N rty [finType of (aT*bT)] _.
  Next Obligation.
    rewrite /(cost) /prodCostInstance.
    apply addr_ge0 => //.
  Qed.

Instance prodMovesInstance
         (N : nat) (aT bT : finType)
         `(movesA : MovesClass N aT)
         `(movesB : MovesClass N bT)         
  : MovesClass N [finType of (aT*bT)] :=
  fun (i : 'I_N) =>
    [rel x y : aT*bT | [&& moves i x.1 y.1 & moves i x.2 y.2]].

Instance prodGameInstance
         (N : nat) (rty : realFieldType) (aT bT : finType)
         `(gameA : game aT N rty)
         `(gameB : game bT N rty) 
  : @game [finType of aT*bT] _ _ _ _ _.

Lemma lambda_of_finType (T : finType) `(smooth T) :
  lambda of T = lambda of [finType of T].
Proof. by []. Qed.

Lemma mu_of_finType (T : finType) `(smooth T) :
  mu of T = mu of [finType of T].
Proof. by []. Qed.

Module ProdGameTest. Section prodGameTest.
  Context {A B N rty} `{gameA : game A N rty} `{gameB : game B N rty}.
  Variables (t : {ffun 'I_N -> A*A}) (i : 'I_N).
  Check cost i t.
End prodGameTest. End ProdGameTest.

(*In the instance that follows, the "| 0" sets the instance 
  priority (for use in typeclass resolution), with 0 being 
  "highest". Priority 0 ensures that "prodLambda" is preferred 
  over the generic finType clone instance for LambdaClass.*)

Instance prodLambdaInstance
         (rty : realFieldType) (aT bT : finType)
         `(lambdaA : LambdaClass aT rty)
         `(lambdaB : LambdaClass bT rty)  
  : @LambdaClass [finType of (aT*bT)] rty | 0 :=
  maxr (lambda of aT) (lambda of bT).

Program Instance prodLambdaAxiomInstance
         (rty : realFieldType) (aT bT : finType)
         `(lambdaA : LambdaAxiomClass aT rty)
         `(lambdaB : LambdaAxiomClass bT rty)
  : @LambdaAxiomClass [finType of (aT*bT)] rty _.
Next Obligation.
  rewrite /lambda_val /prodLambdaInstance.
  by rewrite ler_maxr; apply/orP; left; apply: lambda_pos.
Qed.

Lemma lambdaA_le_prodLambda N rty aT bT
      `(gameA : smooth aT N rty)
      `(gameB : smooth bT N rty) :
  lambda of [finType of aT] <= lambda of [finType of aT*bT].
Proof. by rewrite /prodLambdaInstance; rewrite ler_maxr; apply/orP; left. Qed.

Lemma lambdaB_le_prodLambda N rty aT bT
      `(gameA : smooth aT N rty)
      `(gameB : smooth bT N rty) :
  lambda of [finType of bT] <= lambda of [finType of aT*bT]. 
Proof. by rewrite /prodLambdaInstance; rewrite ler_maxr; apply/orP; right. Qed.

Instance prodMuInstance
         (rty : realFieldType) (aT bT : finType)
         `(muA : MuClass aT rty)
         `(muB : MuClass bT rty)
  : @MuClass [finType of (aT*bT)] rty | 0 :=
  maxr (mu of aT) (mu of bT).

Program Instance prodMuAxiomInstance
        (rty : realFieldType) (aT bT : finType)
        `(muA : MuAxiomClass aT rty)
        `(muB : MuAxiomClass bT rty)
  : @MuAxiomClass [finType of (aT*bT)] rty _ | 0.
Next Obligation.
  rewrite /mu_val /prodMuInstance ler_maxr; apply/andP; split.
  { apply/orP; left; apply: mu_pos. }
  by rewrite ltr_maxl; apply/andP; split; apply: mu_lt1.
Qed.  

Lemma muA_le_prodMu N rty aT bT
      `(gameA : smooth aT N rty)
      `(gameB : smooth bT N rty) :
  mu of [finType of aT] <= mu of [finType of aT*bT].
Proof. by rewrite /prodMuInstance; rewrite ler_maxr; apply/orP; left. Qed.

Lemma muB_le_prodMu N rty aT bT
      `(gameA : smooth aT N rty)
      `(gameB : smooth bT N rty) :
  mu of [finType of bT] <= mu of [finType of aT*bT]. 
Proof. by rewrite /prodMuInstance; rewrite ler_maxr; apply/orP; right. Qed.

Lemma prodSmoothnessAxiom' {aT bT N rty}
      `{smoothA : smooth aT N rty}
      `{smoothB : smooth bT N rty}
      (t t' : ((aT*bT) ^ N)%type) :
  \sum_(i < N)
    (cost) i [ffun j => ([ffun j0 => if i == j0 then t' j0 else t j0] j).1] =
  \sum_(i < N)
    (cost) i ([fun j0 => [ffun j => if i == j then (j0 j).1 else (t j).1]] t').
Proof.
  apply eq_bigr.
  move => i _.
  apply f_equal.
  rewrite -ffunP.
  rewrite /eqfun.
  move => x.
  rewrite !ffunE.
  case: (i ==x) => //.
Qed.

Lemma prodSmoothnessAxiom {aT bT N rty}
      `{smoothA : smooth aT N rty}
      `{smoothB : smooth bT N rty}
  (t t' : ((aT*bT) ^ N)%type) :
  valid_Move t t' -> 
  \sum_(i : 'I_N) cost i (upd i t t') <=
  lambda of [finType of aT*bT] * Cost t' + mu of [finType of aT*bT] * Cost t.
Proof.
  move => h.
  rewrite /Cost!big_split.
  rat_to_ring.
  set m := mu of [finType of aT * bT].
  set l := lambda of [finType of aT * bT]. 
  rewrite !mulrDr.
  rewrite [m * _ + _] addrC -addrA [l * _ + (m * _ + _)]
          addrA [(l * _ + _) + _] addrC !addrA -addrA.
  apply ler_add.
  apply ler_trans with
    (y := (lambda of [finType of aT]) *
          (\sum_(i < N) (cost) i [ffun j => (t' j).1]) +
          (mu of [finType of aT]) *
          (\sum_(i < N) (cost) i [ffun j => (t j).1])).
  rewrite -lambda_of_finType.
  rewrite -mu_of_finType.
  eapply (ler_trans _
    (smooth_ax _ )).
  apply ler_add;
  rewrite ler_wpmul2r => //.
  apply big_rec => //=.
  move => i x _ h'.
  apply addr_ge0 => //=.
  apply (lambdaA_le_prodLambda smoothA) => //.
  apply big_rec => //=.
  move => i x _ h'.
  apply addr_ge0 => //=.
  apply (muA_le_prodMu smoothA) => //.
  apply ler_trans with
    (y := (lambda of [finType of bT]) *
          (\sum_(i < N) (cost) i [ffun j => (t' j).2]) +
          (mu of [finType of bT]) *
          (\sum_(i < N) (cost) i [ffun j => (t j).2])).
  rewrite -lambda_of_finType.
  rewrite -mu_of_finType.
  eapply (ler_trans _
    (smooth_ax _ )).
  apply ler_add;
  rewrite ler_wpmul2r => //.
  apply big_rec => //=.
  move => i x _ h'.
  apply addr_ge0 => //=.
  apply (lambdaB_le_prodLambda smoothA) => //.
  apply big_rec => //=.
  move => i x _ h'.
  apply addr_ge0 => //=.
  apply (muB_le_prodMu smoothA) => //.
  Unshelve.
  rewrite ler_eqVlt.
  apply /orP.
  left.
  apply/eqP.
  apply eq_bigr.
  move => i _.
  apply f_equal.
  rewrite /upd.
  rewrite -ffunP.
  rewrite /eqfun.
  move => x.
  rewrite !ffunE.
  case: (i ==x) => //.
  rewrite /valid_Move /Move.
  move => i. rewrite ffunE.
  rewrite /valid_Move /Move in h.
  specialize (h i).
  move/andP: h => /= => h.
  case: h => h h0.
  apply /andP.
  split.
  rewrite ffunE in h. 
  rewrite ffunE.
  rewrite eq_refl.
  rewrite eq_refl in h.
  rewrite ffunE.
  rewrite /(moves) /prodMovesInstance in h.
  simpl in h.
  move/andP in h.
  case: h => h h' => //.
  apply /forallP.
  move => x.
  apply/implyP.
  move/implyP: h0 => h0 h1.
  apply /eqP.
  rewrite !ffunE.
  rewrite ifN_eq => //.
  rewrite ler_eqVlt.
  apply /orP.
  left.
  apply/eqP.
  apply eq_bigr.
  move => i _.
  apply f_equal.
  rewrite /upd.
  rewrite -ffunP.
  rewrite /eqfun.
  move => x.
  rewrite !ffunE.
  case: (i ==x) => //.
  rewrite /valid_Move /Move.
  move => i. rewrite ffunE.
  rewrite /valid_Move /Move in h.
  specialize (h i).
  move/andP: h => /= => h.
  case: h => h h0.
  apply /andP.
  split.
  rewrite ffunE in h. 
  rewrite ffunE.
  rewrite eq_refl.
  rewrite eq_refl in h.
  rewrite ffunE.
  rewrite /(moves) /prodMovesInstance in h.
  simpl in h.
  move/andP in h.
  case: h => h h' => //.
  apply /forallP.
  move => x.
  apply/implyP.
  move/implyP: h0 => h0 h1.
  apply /eqP.
  rewrite !ffunE.
  rewrite ifN_eq => //.
Qed.

Instance prodSmoothAxiomInstance {aT bT N rty}
         `{smoothA : smooth aT N rty}
         `{smoothB : smooth bT N rty}
  : @SmoothnessAxiomClass [finType of (aT*bT)] N rty _ _ _ _ _ _ _ _
  := prodSmoothnessAxiom.

Instance prodSmoothInstance {aT bT N rty}
         `{smoothA : smooth aT N rty}
         `{smoothB : smooth bT N rty}
  : @smooth [finType of (aT*bT)] N rty _ _ _ _ _ _ _ _ _.

Module ProdSmoothTest. Section prodSmoothTest.
  Context {A B N rty} `{gameA : smooth A N rty} `{gameB : smooth B N rty}.
  Lemma x0 (t : {ffun 'I_N -> A*B}) (i : 'I_N) : cost i t == 0. Abort.
  Lemma x1 (t : {ffun 'I_N -> A*B}) (i : 'I_N) : cost i t <= lambda of A. Abort.
  Lemma x2 (t : {ffun 'I_N -> A*B}) (i : 'I_N) :
    mu of [finType of A * B] == lambda of [finType of A * B]. Abort.
End prodSmoothTest. End ProdSmoothTest.

(** Scalar Games c * A *)

Section ScalarType.
Variable rty : realFieldType.
  
Inductive Scalar : rty -> Type :=
  mkScalar : forall (c : rty), Scalar c.

Definition Scalar_eq c (s1 s2 : Scalar c) : bool := 
  match s1, s2 with
  | mkScalar r1, mkScalar r2 => r1 == r2
  end.
Lemma Scalar_eqP c : Equality.axiom (@Scalar_eq c).
Proof. by case=> s; case=> r /=; rewrite eq_refl; constructor. Qed.
  
Definition Scalar_eqMixin c := EqMixin (@Scalar_eqP c).
Canonical Scalar_eqType c :=
  Eval hnf in EqType (@Scalar c) (Scalar_eqMixin c).

Definition scalar (c : rty) (A : finType) :=
  Wrapper [eqType of Scalar c] A.

Definition scalarType (c : rty) (A : finType) :=
  [finType of Wrapper [eqType of Scalar c] A].
End ScalarType.

Class ScalarClass (rty : realFieldType)
  : Type := scalar_val : rty.

Class ScalarAxiomClass (rty : realFieldType)
      `(ScalarClass rty)
  : Type := scalar_axiom : 0 < scalar_val.

Instance scalarCostInstance
         (N : nat) (rty : realFieldType) (A : finType)
         `(costA : CostClass N rty A)
         `(scalarA : ScalarClass rty)
  : CostClass N rty (scalarType scalar_val A) :=
  fun (i : 'I_N) (f : {ffun 'I_N -> scalarType scalar_val A}) =>
    scalar_val * cost i (unwrap_ffun f).

Program Instance  scalarCostAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(costA : CostAxiomClass N rty A)
        `(scalarA : ScalarAxiomClass rty)        
  : @CostAxiomClass
      N rty
      (scalarType scalar_val A)
      (@scalarCostInstance N rty _ _ _).
Next Obligation.
  rewrite /(cost) /scalarCostInstance mulr_ge0=> //.
  by apply: ltrW.
Qed.

(*Uses the generic move instance for wrapped types*)

Instance scalarGameInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(ScalarAxiomClass rty) 
        `(gameA : game A N rty)
  : @game (scalarType scalar_val A) N rty 
          (@scalarCostInstance N rty A _ _)
          (@scalarCostAxiomInstance N rty A _ _ _ _) _.

Module ScalarGameTest. Section scalarGameTest.
  Context {A N rty} `{gameA : game A N rty} `{scalarA : ScalarAxiomClass rty}.
  Variables (t : {ffun 'I_N -> scalarType scalar_val A}) (i : 'I_N).
  Check cost i t.
End scalarGameTest. End ScalarGameTest.

Instance scalarLambdaInstance
         (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(lambdaA : LambdaClass A rty)
  : @LambdaClass (scalarType scalar_val A) rty | 0 := lambda of A.

Program Instance scalarLambdaAxiomInstance
        (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(lambdaA : LambdaAxiomClass A rty)
  : @LambdaAxiomClass (scalarType scalar_val A) rty _ | 0.

Instance scalarMuInstance
         (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(lambdaA : MuClass A rty)
  : @MuClass (scalarType scalar_val A) rty | 0 := mu of A.

Program Instance scalarMuAxiomInstance
        (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(lambdaA : MuAxiomClass A rty)
  : @MuAxiomClass (scalarType scalar_val A) rty _ | 0.

Program Instance scalarSmoothAxiomInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{scalarA : ScalarAxiomClass rty}
  : @SmoothnessAxiomClass (scalarType scalar_val A) N rty _ _ _ _ _ _ _ _.
Next Obligation.
  rewrite /Cost /(cost) /scalarCostInstance.
  rewrite /lambda_val /scalarLambdaInstance.
  rewrite /mu_val /scalarMuInstance.
  rewrite -3!mulr_sumr.
  rewrite mulrA [lambda of A * _]mulrC -mulrA.
  rewrite [mu of A * _]mulrA [mu of A * _]mulrC -mulrA.
  rewrite -mulrDr; apply: ler_mull=> //.
  have H4: valid_Move (T:=A) (unwrap_ffun t) (unwrap_ffun t').
  { by apply: valid_Move_unwrap. }
  by rewrite unwrap_ffun_simpl unwrap_eta; apply: smooth_ax.
Qed.

Instance scalarSmoothInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{scalarA : ScalarAxiomClass rty}
  : @smooth (scalarType scalar_val A) N rty _ _ _ _ _ _ _ _ _.

Module ScalarSmoothTest. Section scalarSmoothTest.
  Context {A N rty} `{gameA : smooth A N rty} `{scalarA : ScalarAxiomClass rty}.
  Lemma x0 (t : {ffun 'I_N -> (scalarType scalar_val A)}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> (scalarType scalar_val A)}) (i : 'I_N) :
    cost i t == lambda of (scalarType scalar_val A). Abort.
End scalarSmoothTest. End ScalarSmoothTest.

(** Bias Games c + A *)

Section BiasType.
Variable rty : realFieldType.
  
Inductive Bias : rty -> Type :=
  mkBias : forall c : rty, Bias c.

Definition Bias_eq c (s1 s2 : Bias c) : bool := 
  match s1, s2 with
  | mkBias r1, mkBias r2 => r1 == r2
  end.
Lemma Bias_eqP c : Equality.axiom (@Bias_eq c).
Proof. by case=> s; case=> r /=; rewrite eq_refl; constructor. Qed.
  
Definition Bias_eqMixin c := EqMixin (@Bias_eqP c).
Canonical Bias_eqType c :=
  Eval hnf in EqType (@Bias c) (Bias_eqMixin c).

Definition bias (c : rty) (A : finType) :=
  Wrapper [eqType of Bias c] A.

Definition biasType (c : rty) (A : finType) :=
  [finType of Wrapper [eqType of Bias c] A].
End BiasType.

Instance biasCostInstance
         (N : nat) (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(costA : CostClass N rty A)
  : CostClass N rty (biasType scalar_val A) :=
  fun (i : 'I_N) (f : {ffun 'I_N -> biasType scalar_val A}) =>
    scalar_val + cost i (finfun (fun j => unwrap (f j))).

Program Instance  biasCostAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(costA : CostAxiomClass N rty A)
  : @CostAxiomClass N rty (biasType scalar_val A) (@biasCostInstance N rty _ scalar_val _).
Next Obligation.
  rewrite /(cost) /biasCostInstance addr_ge0 => //.
  by apply: ltrW; apply scalar_axiom.
Qed.

(*Uses the generic move instance for wrapped types*)

Instance biasGameInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(gameA : game A N rty)
        `(scalarA : ScalarAxiomClass rty)
  : @game (biasType scalar_val A) N rty 
          (@biasCostInstance N rty A scalar_val _)
          (@biasCostAxiomInstance N rty A _ _ _ _) _.

Module BiasGameTest. Section biasGameTest.
  Context {A N rty} `{gameA : game A N rty} `{scalarA : ScalarAxiomClass rty}.
  Variables (t : {ffun 'I_N -> biasType scalar_val A}) (i : 'I_N).
  Check cost i t.
End biasGameTest. End BiasGameTest.

Instance biasLambdaInstance
         (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(lambdaA : LambdaClass A rty)
  : @LambdaClass (biasType scalar_val A) rty | 0 := lambda of A.

Program Instance biasLambdaAxiomInstance
        (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(lambdaA : LambdaAxiomClass A rty)
  : @LambdaAxiomClass (biasType scalar_val A) rty _ | 0.

Instance biasMuInstance
         (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(lambdaA : MuClass A rty)
  : @MuClass (biasType scalar_val A) rty | 0 := mu of A.

Program Instance biasMuAxiomInstance
        (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(lambdaA : MuAxiomClass A rty)
  : @MuAxiomClass (biasType scalar_val A) rty _ | 0.
                                          
Class LambdaMuGe1Class (A : finType) N (rty : realFieldType) `(smooth A N rty)
  : Type := lambdaMu_ge1 : 1 <= lambda of A + mu of A.

Program Instance biasSmoothAxiomInstance {A N rty}
        `{smoothA : smooth A N rty}
         (LambdaMu_ge1 : LambdaMuGe1Class smoothA)  
        `{scalarA : ScalarAxiomClass rty}
  : @SmoothnessAxiomClass (biasType scalar_val A) N rty _ _ _ _ _ _ _ _.
Next Obligation.
  rewrite /Cost /(cost) /biasCostInstance.
  rewrite /lambda_val /biasLambdaInstance.
  rewrite /mu_val /biasMuInstance.
  have Hval: valid_Move (T:=A) (unwrap_ffun t) (unwrap_ffun t').
  { by apply: valid_Move_unwrap. }
  rewrite big_split /= !big_distrr /= -2!mulr_sumr 2!big_split /= 2!mulrDr.
  rewrite addrA [lambda of A * _ + _]addrC.
  rewrite -[(lambda of A * _ + _) + _]addrA.
  rewrite [lambda of A * _ + _]addrC.
  rewrite -[(lambda of A * _ + _) + _ + _]addrA; apply: ler_add.
  { rewrite -mulrDl; apply: ler_pemull.
    by apply: sumr_ge0=> _ _; apply: ltrW; apply: scalar_axiom.
    by apply: lambdaMu_ge1. }
  by rewrite unwrap_ffun_simpl unwrap_eta; apply: smooth_ax.
Qed.

Instance biasSmoothInstance {A N rty}
         `{smoothA : smooth A N rty}
         (LambdaMu_ge1 : LambdaMuGe1Class smoothA)
         `{scalarA : ScalarAxiomClass rty}
  : @smooth (biasType scalar_val A) N rty _ _ _ _ _ _ _ _ _.

Module BiasSmoothTest. Section biasSmoothTest.
  Context {A N rty} `{gameA : smooth A N rty} `{scalarA : ScalarAxiomClass rty}.
  Context (LambdaMu_ge1 : LambdaMuGe1Class gameA).
  Lemma x0 (t : {ffun 'I_N -> (biasType scalar_val A)}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> (biasType scalar_val A)}) (i : 'I_N) :
    cost i t == lambda of (biasType scalar_val A). Abort.
End biasSmoothTest. End BiasSmoothTest.

(** Unit Games c(s) = 0 *)

Section UnitType.
Variable rty : realFieldType.
  
Inductive Unit : Type := mkUnit : Unit.

Definition Unit_eq (s1 s2 : Unit) : bool := true.

Lemma Unit_eqP : Equality.axiom Unit_eq.
Proof. by case; case; constructor. Qed.
  
Definition Unit_eqMixin := EqMixin Unit_eqP.
Canonical Unit_eqType := Eval hnf in EqType Unit Unit_eqMixin.

Definition unitTy := Wrapper [eqType of Unit] [finType of unit].
Definition unitType := [finType of unitTy].
End UnitType.

Instance unitCostInstance
         (N : nat) (rty : realFieldType)
  : CostClass N rty unitType :=
  fun (i : 'I_N) (f : {ffun 'I_N -> unitType}) => 0.

Program Instance  unitCostAxiomInstance
        (N : nat) (rty : realFieldType)
  : @CostAxiomClass N rty unitType (@unitCostInstance N rty).

Instance unitMovesClass (N : nat)
  : @MovesClass N unitType := fun _ => [rel _ _ | true].

Program Instance unitGameInstance
        (N : nat) (rty : realFieldType) 
  : @game unitType N rty 
          (@unitCostInstance N rty)
          (@unitCostAxiomInstance N rty) _.

Module UnitGameTest. Section unitGameTest.
  Context {N rty} `{gameA : game unitType N rty}.
  Variables (t : {ffun 'I_N -> unitType}) (i : 'I_N).
  Check cost i t.
End unitGameTest. End UnitGameTest.

Instance unitLambdaInstance
         (rty : realFieldType) 
  : @LambdaClass unitType rty | 0 := 1.

Program Instance unitLambdaAxiomInstance
        (rty : realFieldType) 
  : @LambdaAxiomClass unitType rty _ | 0.
Next Obligation. by apply: ler01. Qed.

Instance unitMuInstance
         (rty : realFieldType)
  : @MuClass unitType rty | 0 := 0.

Program Instance unitMuAxiomInstance
        (rty : realFieldType)
  : @MuAxiomClass unitType rty _ | 0.
Next Obligation.
  apply/andP; split; first by apply: lerr.
  by apply: ltr01.
Qed.
                                          
Program Instance unitSmoothAxiomInstance {N rty}
  : @SmoothnessAxiomClass unitType N rty _ _ _ _ _ _ _ _.
Next Obligation.
  rewrite mul1r mul0r addr0; have ->: t = t'.
  { apply/ffunP; case => m i; case: (t _)=> s; case: (t' _)=> s'.
    by f_equal; case: s; case: s'. }
  by [].
Qed.  

Instance unitSmoothInstance {N rty}
  : @smooth unitType N rty _ _ _ _ _ _ _ _ _.

Module UnitSmoothTest. Section unitSmoothTest.
  Context {N rty} `{gameA : smooth unitType N rty}.
  Lemma x0 (t : {ffun 'I_N -> unitType}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> unitType}) (i : 'I_N) :
    cost i t == lambda of unitType. Abort.
End unitSmoothTest. End UnitSmoothTest.

(** Affine Games: C(x) = ax + b, 0 <= a, 0 <= b *)

Section AffineGame.
Variable rty : realFieldType.
Context `(scalarA : ScalarClass rty) `(@ScalarAxiomClass _ scalarA).
Context `(scalarB : ScalarClass rty) `(@ScalarAxiomClass _ scalarB).

Variables (A : finType) (N : nat).
Context `(Boolable A).
Context `(game A N rty).

Definition affineType : Type :=
  scalarType (@scalar_val _ scalarA) A *
  scalarType (@scalar_val _ scalarB) (singletonType A).

Section affineGameTest.
Variable t : {ffun 'I_N -> affineType}.
Variable i : 'I_N.
Check cost i t.
End affineGameTest.
End AffineGame.