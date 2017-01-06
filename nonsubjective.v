Set Implicit Arguments.
Unset Strict Implicit.

Require Import pcm.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema dist subjective.

Local Open Scope ring_scope.

(** This module defines an interface over smooth subjective games. *)

Module NGame.
  Section ClassDef.
    Record mixin_of T :=
      Mixin { mx_lambda : rat;
              mx_mu : rat;
              mx_N : nat;
              mx_cost : forall (i : 'I_mx_N), {ffun 'I_mx_N -> T} -> rat;
              mx_cost_pos : forall (i : 'I_mx_N) a, 0 <= mx_cost i a;
              mx_lambda_pos : 0 <= mx_lambda;
              mx_mu_pos : 0 <= mx_mu;              
              mx_mu_lt1 : mx_mu < 1;
              mx_Cost (a : {ffun 'I_mx_N -> T}) := \sum_(i : 'I_mx_N) mx_cost i a;
              mx_smooth :
                forall (a a' : {ffun 'I_mx_N -> T}),
                  \sum_(i : 'I_mx_N) mx_cost i [ffun j => if i == j then a' i else a j] <=
                  mx_lambda * mx_Cost a' + mx_mu * mx_Cost a
              }.
    
    Record class_of T := Class {base : Finite.class_of T; mixin : mixin_of T}.
    Local Coercion base : class_of >-> Finite.class_of.
    
    Structure type := Pack {sort; _ : class_of sort; _ : Type}.
    Local Coercion sort : type >-> Sortclass.
    Variables (T : Type) (cT : type).
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).
    
    Definition pack m :=
      fun b bT & phant_id (Finite.class bT) b => Pack (@Class T b m) T.

    (* Inheritance *)
    Definition eqType := @Equality.Pack cT xclass xT.
    Definition finType := @Finite.Pack cT xclass xT.

    Definition N := @mx_N _ (mixin class).
    Definition cost := @mx_cost _ (mixin class).
    Definition Cost := @mx_Cost _ (mixin class).
    Definition lambda := @mx_lambda _ (mixin class).
    Definition mu := @mx_mu _ (mixin class).    
  End ClassDef.

  Module Import Exports.
    Coercion base : class_of >-> Finite.class_of.
    Coercion sort : type >-> Sortclass.
    Coercion eqType : type >-> Equality.type.
    Coercion finType : type >-> Finite.type.
    Canonical eqType.
    Canonical finType.
    Notation game := type.
    Notation gameMixin := mixin_of.
    Notation GameType T m := (@pack T m _ _ id).
    Notation "[ 'game' 'of' T 'for' cT ]" :=
      (@clone T cT _ idfun)
        (at level 0, format "[ 'game'  'of'  T  'for'  cT ]") : form_scope.
    Notation "[ 'game' 'of' T ]" :=
      (@clone T _ _ id)
        (at level 0, format "[ 'game'  'of'  T ]") : form_scope.

    Section defs.
      Variable T : game.
      Definition N : nat := (@N T).
      Definition cost : 'I_N -> {ffun 'I_N -> T} -> rat := @cost T.
      Definition Cost : {ffun 'I_N -> T} -> rat := @Cost T.
      Definition lambda : rat := @lambda T.
      Definition mu : rat := @mu T.
      Lemma cost_pos (i : 'I_N) a : 0 <= cost i a.
      Proof. apply: (@mx_cost_pos _ (mixin (class T))). Qed.
      Lemma lambda_pos : 0 <= lambda.
      Proof. by apply: (mx_lambda_pos (mixin (class T))). Qed.
      Lemma mu_pos : 0 <= mu.
      Proof. by apply: (mx_mu_pos (mixin (class T))). Qed.
      Lemma mu_lt1 : mu < 1.
      Proof. by apply: (mx_mu_lt1 (mixin (class T))). Qed.
      Lemma smooth (a a' : {ffun 'I_N -> T}) :
        \sum_(i : 'I_N) cost i [ffun j => if i == j then a' i else a j] <=
        lambda * Cost a' + mu * Cost a.
      Proof. by apply: (@mx_smooth _ (mixin (class T))). Qed.
    End defs.
    Arguments cost [T] _ _.
    Arguments Cost [T] _.    
    Arguments cost_pos [T] _ _.
    Arguments smooth [T a a'].
  End Exports.
End NGame.
Export NGame.Exports.



Module ParallelGame.
  Section parallelGame.
    Local Open Scope rat_scope.

    Variable A : Game.Exports.game.
    Variable N : nat.

    Definition T := (Game.sort A).
    Definition lambda := Game.Exports.lambda A.
    Definition mu := Game.Exports.mu A.

    Definition cost (i : 'I_N)  f :=
      \sum_(j : 'I_N | i != j) (@Game.Exports.cost A (f i) (f j)).
    
    Lemma simpl_mix_state : forall a' a,
      \sum_(i : 'I_N) cost i [ffun j => if i == j then a' i else a j] =
      \sum_(i : 'I_N) (\sum_(j : 'I_N | i != j)
        (@Game.Exports.cost A (a' i) (a j))).
    Proof.
      move => a' a. apply eq_bigr.
      move => i h. rewrite /cost.
      apply eq_bigr. move => j h1.
      rewrite !ffunE eq_refl ifN_eq => //.
    Qed.
    
    Section setGames.
      (** These define the ordered pairs we want in order to
          bring this under one big sum for rewriting **)
    
      (* [iXord i] => {(i,0), (i,1), ... (i, N-1)} *)
      Definition iXord (i : 'I_N) : {set ('I_N * 'I_N)%type} :=
        [set x | (x.1 == i) && (x.2 != i) ].

      (* Like iXord, but only if j < i *)
      Definition iXord_lt (i : 'I_N) : {set ('I_N * 'I_N)%type} :=
        [set x | (x.1 == i) && ((nat_of_ord x.2) < (nat_of_ord i))%N ].

      (* Like iXord, but only if j > i *)
      Definition iXord_gt (i : 'I_N) : {set ('I_N * 'I_N)%type} :=
        [set x | (x.1 == i) && ((nat_of_ord x.2) > (nat_of_ord i))%N ].

      Lemma iXord_spec1 : 
        forall i x, x \in (iXord i) -> x.1 = i.
      Proof.
        move => i x h.
        rewrite /iXord inE in h.
        move/andP : h.
        case => h1 h2.
        move/eqP: h1.
        auto.
      Qed.

      Lemma iXord_spec2 :
        forall i x, x \in (iXord i) -> x.2 <> i.
      Proof.
        move => i x h.
        rewrite /iXord inE in h.
        move/andP : h.
        case => h1 h2.
        move/eqP: h2.
        auto.
      Qed.

      Lemma iXord_lt_spec1 :
        forall i x, x \in (iXord_lt i) -> x.1 = i.
      Proof.
        move => i x h.
        rewrite /iXord inE in h.
        move/andP : h.
        case => h1 h2.
        move/eqP: h1.
        auto.
      Qed.

      Lemma iXord_lt_spec2 :
        forall i x, x \in (iXord_lt i) ->
          ((nat_of_ord x.2) < (nat_of_ord i))%N.
      Proof.
        move => i x h.
        rewrite /iXord inE in h.
        move/andP : h.
        case => h1 h2.
        auto.
      Qed.

      Lemma iXord_gt_spec1 :
        forall i x, x \in (iXord_gt i) -> x.1 = i.
      Proof.
        move => i x h.
        rewrite /iXord inE in h.
        move/andP : h.
        case => h1 h2.
        move/eqP: h1.
        auto.
      Qed.

      Lemma iXord_gt_spec2 :
        forall i x, x \in (iXord_gt i) ->
          ((nat_of_ord x.2) > (nat_of_ord i))%N.
      Proof.
        move => i x h.
        rewrite /iXord inE in h.
        move/andP : h.
        case => h1 h2.
        auto.
      Qed.

      Lemma iX_lt_gt_disjoint :
        forall i j, [disjoint (iXord_lt i) & (iXord_gt j)].
      Proof.
        move => i j.
        apply /setDidPl.
        rewrite /setD.
        apply /eqP.
        rewrite eqEsubset.
        apply /andP.
        split;
        apply /subsetP;
        move => x h0;
        rewrite inE; rewrite inE in h0;
        apply /andP;
        move/andP: h0; case => h0 h1;
        split.
        apply /eqP.
        apply iXord_lt_spec1. auto.
        apply iXord_lt_spec2. auto.
        rewrite inE.
        apply /negP.
        case/andP => h2 h3.
        move/eqP: h0.
        move /eqP: h2.
        move => h0 h2; subst.
        have h : (x.1 < x.1)%N. apply (ltn_trans h3 h1).
        rewrite ltnn in h => //.
        rewrite /iXord_lt inE.
        apply /andP; split => //.
      Qed.

      Lemma iXord_eq :
      forall i, (iXord) i = (iXord_lt i) :|: (iXord_gt i).
      Proof.
        move => i.
        apply /eqP.
        rewrite eqEsubset.
        apply /andP.
        split;
        apply /subsetP;
        move => x h0;
        rewrite inE;
        rewrite inE in h0.
        move/andP: h0.
        case => h0 h1.
        rewrite !inE.
        apply /orP.
        rewrite neq_ltn in h1.
        case/orP : h1;
        move => h1;
        [left | right];
        apply /andP;
        split => //.
        move/orP: h0.
        case => h0;
        apply /andP;
        split.
        apply iXord_lt_spec1 in h0.
        apply /eqP => //.
        apply iXord_lt_spec2 in h0.
        rewrite neq_ltn.
        apply /orP.
        left => //.
        apply iXord_gt_spec1 in h0.
        apply /eqP => //.
        apply iXord_gt_spec2 in h0.
        rewrite neq_ltn.
        apply /orP.
        right => //.
      Qed.

      Lemma disjoint_iXord_lt :
        forall i j, i != j -> [disjoint (iXord_lt i) & (iXord_lt j)].
      Proof.
        move => i j h0.
        apply /setDidPl.
        rewrite /setD.
        apply /eqP.
        rewrite eqEsubset.
        apply /andP.
        split;
        apply /subsetP;
        move => x h1;
        rewrite inE; rewrite inE in h1;
        apply /andP;
        move/andP: h1; case => h1 h2;
        split.
        apply /eqP. apply iXord_lt_spec1 in h2 => //.
        apply iXord_lt_spec2 in h2 => //.
        rewrite inE.
        apply/negP.
        case/andP => h3 h4.
        case/eqP in h0.
        move/eqP in h3. move /eqP in h1.
        subst => //.
        rewrite inE.
        apply /andP; split => //.
      Qed.

      Lemma disjoint_iXord_gt :
        forall i j, i != j -> [disjoint (iXord_gt i) & (iXord_gt j)].
      Proof.
        move => i j h0.
        apply /setDidPl.
        rewrite /setD.
        apply /eqP.
        rewrite eqEsubset.
        apply /andP.
        split;
        apply /subsetP;
        move => x h1;
        rewrite inE; rewrite inE in h1;
        apply /andP;
        move/andP: h1; case => h1 h2;
        split.
        apply /eqP. apply iXord_gt_spec1 in h2 => //.
        apply iXord_gt_spec2 in h2 => //.
        rewrite inE.
        apply/negP.
        case/andP => h3 h4.
        case/eqP in h0.
        move/eqP in h3. move /eqP in h1.
        subst => //.
        rewrite inE.
        apply /andP; split => //.
      Qed.

      Lemma disjoint_iXord :
        forall i j, i != j -> [disjoint (iXord i) & (iXord j)].
      Proof.
        move => i j h.
        apply /setDidPl.
        rewrite /setD.
        apply /eqP.
        rewrite eqEsubset.
        apply /andP.
        split;
        apply /subsetP;
        move => x h1;
        rewrite inE; rewrite inE in h1;
        apply /andP;
        move/andP: h1; case => h1 h2;
        split => //.
        apply /eqP. apply iXord_spec1 in h2 => //.
        apply /eqP.
        apply iXord_spec2 in h2 => //.
        apply /negP.
        move => h3.
        case/eqP: h.
        apply iXord_spec1 in h3;
        case/eqP: h1. move => h1.
         subst => //. 
        rewrite inE.
        apply /andP; split => //.
      Qed.

      (** Definitions for the FULL sets of pairs **)
      (*
                          -   (0,1) (0,2) ...
        [ordXord] => {  (1,0)   -   (1,2) ...  }
                        (2,0) (2,1)   -   ...
      *)
      Definition ordXord :=
        \bigcup_(i : 'I_N) (iXord i).
    
      (*
                            -   (0,1) (0,2) ...
        [ordXord_lt] => {   -     -   (1,2) ...  }
                            -     -   -   ...
        *)    
      Definition ordXord_lt :=
        \bigcup_(i : 'I_N) (iXord_lt i).

      Definition ordXord_gt :=
        \bigcup_(i : 'I_N) (iXord_gt i).
      (*
                             -      -     -  ...
        [ordXord_gt] => {  (1,0)    -     -  ...  }
                           (2,0)  (2,1)   -  ...
      *)  

      Lemma ordXord_eq :
        ordXord = ordXord_lt :|: ordXord_gt.
      Proof.
        rewrite /ordXord /ordXord_gt /ordXord_lt.
        rewrite -big_split => /=.
        apply eq_bigr.
        move => i _.
        apply iXord_eq.
      Qed.

      Lemma disjoint_sum_split : forall (A : finType) (p1 p2 : pred A) (F : A -> rat),
        [disjoint p1 & p2] ->
        \sum_(x in [predU p1 & p2]) F x = \sum_(x in p1) F x + \sum_(x in p2) F x.
      Proof. by apply: bigU. Qed.

      Lemma ordXord_rewrite' : forall (A : finType) (s1 s2 : {set A}) (F : A -> rat),
        [disjoint s1 & s2] ->
        \sum_(x in (s1 :|: s2)) F x = \sum_(x in s1) F x + \sum_(x in s2) F x.
      Proof.
        move=> X s1 s2 F H.
        set p1 := [pred x | x \in s1].
        set p2 := [pred x | x \in s2]. 
        have H2: \sum_(x in s1 :|: s2) F x = \sum_(x in [predU p1 & p2]) F x.
        { by rewrite (eq_big [predU p1 & p2] F)=> // x; rewrite in_set. }
        rewrite H2.
        rewrite disjoint_sum_split=> //.
      Qed.        

      Lemma ordXord_rewrite :
        forall (F : 'I_N -> 'I_N -> rat),
          \sum_(x in ordXord) F x.1 x.2 =
          \sum_(x in ordXord_lt) F x.1 x.2 +
            \sum_(x in ordXord_gt) F x.1 x.2.
      Proof.
        move => F.
        rewrite ordXord_eq ordXord_rewrite' => //.
        apply bigcup_disjoint.
        move => i _.
        rewrite disjoint_sym.
        apply bigcup_disjoint.
        move => j _.
        rewrite disjoint_sym.
        apply iX_lt_gt_disjoint.
      Qed. 

      Definition mixed_cost a a' : 'I_N -> 'I_N -> rat :=
        (fun i j => @Game.Exports.cost A (a' i) (a j)).
     
      Definition mixed_cost' a a' : ('I_N*'I_N)%type -> rat :=
        (fun x => @Game.Exports.cost A (a' x.1) (a x.2)).

      Lemma mixedStateSet a a':
        \sum_(i : 'I_N) (\sum_(j : 'I_N | i != j) (mixed_cost a a') i j) =
        \sum_(x in ordXord) (mixed_cost a a') x.1 x.2.
      Proof.
        rewrite pair_big_dep; rat_to_ring; apply eq_bigl.
        rewrite /eqfun=> x; rewrite /ordXord.
        case H: (x.1 != x.2).
        { symmetry; apply/bigcupP; exists x.1=> //.
          rewrite /iXord in_set; apply/andP; split=> //.
          by apply/eqP=> H2; rewrite -H2 eqxx in H. }
        case H2: (x \in _)=> //; case: (bigcupP H2)=> i _.
        rewrite /iXord in_set; case/andP=> H3 H4.
        case: (eqP H3)=> H5; subst; move: H; case H: (x.1 == x.2)=> //=.
        by move: (esym (eqP H))=> H5; rewrite H5 eqxx in H4.
      Qed.        
     
    Lemma mixedSet_eq a a':
        \sum_(x in ordXord) (mixed_cost a a') x.1 x.2 =
        \sum_(x in ordXord_lt) (mixed_cost a a') x.1 x.2 +
          \sum_(x in ordXord_gt) (mixed_cost a a') x.1 x.2.
    Proof.
      rewrite ordXord_rewrite. reflexivity.
    Qed.

    Definition swap_pair {X : finType} (x : (X*X)) := (x.2, x.1).
    
    Lemma sum_imset (T U : finType) (rty : realFieldType)
          (s : {set U}) (F : T -> rty) (G : U -> T)
          (H : {in s &, injective G}) :
      \sum_(x in s) (F \o G) x = \sum_(x in G @: s) F x.
    Proof. by symmetry; apply: big_imset. Qed.

    Lemma swap_involutive (T : finType) (p : T*T) :
      swap_pair (swap_pair p) = p.
    Proof. by case: p. Qed.
    
    Lemma swap_set_involutive (T : finType) (s : {set T*T}) :
      [set swap_pair x | x in [set swap_pair x | x in s]] = s.
    Proof.
      rewrite /swap_pair; apply/setP; case=> x y.
      case H: ((x,y) \in _).
      { case: (imsetP H); case=> a b; case/imsetP; case=> a' b' H2 /=.
        by case=> -> ->; case=> -> ->; rewrite H2. }
      move: H; case H: ((x,y) \in s)=> //.
      case H2: ((x, y) \in _)=> //.
      move: (mem_imset swap_pair (mem_imset swap_pair H)).
      by rewrite /swap_pair /= H2.
    Qed.
    
    Lemma swap_F_set (T : finType) (rty : realFieldType)
          (s : {set (T*T)}) (F : T*T -> rty) :
      \sum_(x in s) F x = \sum_(x in swap_pair @: s) (F \o swap_pair) x.
    Proof.
      symmetry; rewrite sum_imset; first by rewrite swap_set_involutive.
      case=> x y; case=> x' y'; case/imsetP; case=> a b H.
      rewrite /swap_pair /=; case=> -> ->.
      by case/imsetP; case=> a' b' H' /=; case=> -> ->; case=> -> ->.
    Qed.      

    Lemma ordXord_lt_gt_swap_eq : swap_pair @: ordXord_lt = ordXord_gt.
    Proof.
      rewrite /ordXord_lt /ordXord_gt /iXord_lt /iXord_gt /=; apply/setP=> p.
      case H: (p \in \bigcup_(i < N) _).
      { case: (bigcupP H)=> i _ H2.
        apply/imsetP; exists (swap_pair p).
        apply/bigcupP; exists p.2=> //.
        rewrite in_set; apply/andP; split=> //.
        rewrite in_set in H2; case: (andP H2); move {H H2}.
        by case: p=> x y /=; move/eqP=> ->.
        by rewrite swap_involutive. }
      case H2: (p \in _)=> //.
      move: H H2; case: p=> x y H; case/imsetP; case=> a b.
      case/bigcupP=> i _; rewrite in_set /=; case/andP; case/eqP=> <-.
      move=> H3; rewrite /swap_pair /=; case=> H4 H5; subst a b.
      have H4: ((x, y) \in \bigcup_(i : 'I_N)
                            [set x : ('I_N*'I_N) | x.1 == i & (i < x.2)%N]).
      { apply/bigcupP; exists x=> //; rewrite in_set /=; apply/andP; split=> //. }
      by rewrite H in H4.
    Qed.            

    Lemma ordXord_lt_gt_swap_eq' : swap_pair @: ordXord_gt = ordXord_lt.
    Proof.
      rewrite /ordXord_lt /ordXord_gt /iXord_lt /iXord_gt /=; apply/setP=> p.
      case H: (p \in \bigcup_(i < N) _).
      { case: (bigcupP H)=> i _ H2.
        apply/imsetP; exists (swap_pair p).
        apply/bigcupP; exists p.2=> //.
        rewrite in_set; apply/andP; split=> //.
        rewrite in_set in H2; case: (andP H2); move {H H2}.
        by case: p=> x y /=; move/eqP=> ->.
        by rewrite swap_involutive. }
      case H2: (p \in _)=> //.
      move: H H2; case: p=> x y H; case/imsetP; case=> a b.
      case/bigcupP=> i _; rewrite in_set /=; case/andP; case/eqP=> <-.
      move=> H3; rewrite /swap_pair /=; case=> H4 H5; subst a b.
      have H4: ((x, y) \in \bigcup_(i : 'I_N)
                            [set x : ('I_N*'I_N) | x.1 == i & (x.2 < i)%N]).
      { by apply/bigcupP; exists x=> //; rewrite in_set /=; apply/andP; split. }
      by rewrite H in H4.
    Qed.            

    Lemma ordXord_lt_gt_dual a a' :
      \sum_(x in ordXord_lt) mixed_cost a a' x.1 x.2 =
      \sum_(x in ordXord_gt) mixed_cost a a' x.2 x.1.
    Proof. by rewrite swap_F_set /= ordXord_lt_gt_swap_eq. Qed.

    Lemma ordXord_gt_lt_dual a a' :
      \sum_(x in ordXord_gt) mixed_cost a a' x.1 x.2 =
      \sum_(x in ordXord_lt) mixed_cost a a' x.2 x.1.
    Proof. by rewrite swap_F_set /= ordXord_lt_gt_swap_eq'. Qed.      
  End setGames.
  
  Program Definition mixin : gameMixin T :=
    @NGame.Mixin T lambda mu N cost _ _ _ _ _.
  Next Obligation.
    rewrite /cost; apply big_ind => //.
    ring_to_rat. move => x y h1 h0.
    ring_to_rat. rewrite addr_ge0 => //.
    move => io H0.
    rewrite Game.Exports.cost_pos => //. Qed.
  Next Obligation. apply Game.Exports.lambda_pos. Qed.
  Next Obligation. apply Game.Exports.mu_pos. Qed.
  Next Obligation. apply Game.Exports.mu_lt1. Qed.
  Next Obligation.
    rewrite simpl_mix_state /cost !mixedStateSet
            !mixedSet_eq. rewrite !ordXord_gt_lt_dual.
    rat_to_ring.
    rewrite -!big_split.
    rat_to_ring.
    rewrite !big_distrr -big_split.
    rat_to_ring.
    apply FunGame.leq_sum_rat.
    move => i h.
    rewrite /mixed_cost. 
    ring_to_rat.
    rewrite [lambda * _] mulqC [mu * _] mulqC !mulq_addl
            ![ _ * lambda ] mulqC ![ _ * mu ] mulqC
            !addqA.
    apply Game.Exports.smooth.
  Qed.

  Definition t := GameType T mixin.
  End parallelGame.
End ParallelGame.
              

(** N-player, parallel resource games *)
Module ResourceGame_Np.  
  Section resourceGame_Np.
    Local Open Scope rat_scope.

    Variable N : nat.

    Definition t := ParallelGame.t ResourceGame.t N.

  End resourceGame_Np.
End ResourceGame_Np.

(** N-player, parallel resource games *)
Module LocationGame_Np.
  Section locationGame_Np.
    Local Open Scope rat_scope.

    Variable N : nat.
  
    Definition t := ParallelGame.t LocationGame.t N.

  End locationGame_Np.
End LocationGame_Np.

Module ScalarGame.
  Section scalarGame.
    Local Open Scope ring_scope.
    
    Check ParallelGame.t.

    Variable A : game.
    Definition N := (N A).
    Variable c : rat.
    
    Hypothesis c_pos : 0 <= c.

    Definition cost (n : 'I_N) (f : {ffun 'I_N -> A}) := c * cost n f.
    Definition Cost (f : {ffun 'I_N -> A}) := c * Cost f.

    Definition lambda := lambda A.
    Definition mu := mu A.
    
    Lemma smooth (a a' : {ffun 'I_N -> A}) :
        \sum_(i : 'I_N) cost i [ffun j => if i == j then a' i else a j] <=
        lambda * (\sum_(i < N) cost i a') + mu * (\sum_(i < N) cost i a).
    Proof.
      rewrite /cost /Cost.
      rewrite -![(\sum_(i < N) c * _)] big_distrr.
      rat_to_ring.
      rewrite ![_ * (c * _)] mulrC -!mulrA -mulrDr.
      apply ler_pmul => //.
      apply big_ind => //.
      move => x y h0 h1.
      apply (ler_add h0 h1).
      move => i _.
      apply cost_pos.
      rewrite ![(\sum_(i < N) NGame.Exports.cost i _) * _]mulrC.
      apply smooth.
    Qed.

    Program Definition mixin :=
      @NGame.Mixin A lambda mu N cost _ _ _ _ smooth.
    Next Obligation.
      rewrite /cost mulr_ge0 => //. apply cost_pos. Qed.
    Next Obligation.
      apply lambda_pos. Qed.
    Next Obligation.
      apply mu_pos. Qed.
    Next Obligation.
      apply mu_lt1.
    Qed.

    Definition t := GameType A mixin.

  End scalarGame.
End ScalarGame.  

(** N-Player unit games, with [C(a, b) = 0] for all [a, b] *)

Module UnitGame_N.
  Section unitGame_N.
    Local Open Scope ring_scope.

    Variable N : nat.
    Definition cost (n : 'I_N) (f : {ffun 'I_N -> unit}) : rat := 0.

    Program Definition mixin :=
      @NGame.Mixin unit 0 0 N cost _ _ _ _ _.
    Next Obligation.
      rewrite /cost mul0r.
      apply big_ind => //.
      move => x y h0 h1.
      rewrite add0r in h0, h1.
      apply ler_add => //.
    Qed.

    Definition t := GameType unit mixin. 
  End unitGame_N.
End UnitGame_N.

(* N player Singleton Games *)
Module SingletonGame_N.
  Section singletonGame_N.
    Local Open Scope ring_scope.
    Variable N : nat.
    Definition cost (n : 'I_N) (f : 'I_N -> bool) : rat :=
      if (f n) then 1 else 0.

    Definition lambda : rat := 1.
    Definition mu : rat := 0.

    Lemma smooth (a a' : {ffun 'I_N -> bool}) :
        \sum_(i : 'I_N) cost i [ffun j => if i == j then a' i else a j] <=
        lambda * (\sum_(i < N) cost i a') + mu * (\sum_(i < N) cost i a).
    Proof.
      rewrite !big_distrr -big_split.
      rat_to_ring.
      apply FunGame.leq_sum_rat.
      move => i _.
      rewrite !/cost.
      rewrite ffunE eq_refl.
      case: (a' i); case (a i);
      rewrite /lambda /mu => //.
    Qed.

    Program Definition mixin :=
      @NGame.Mixin bool lambda mu N cost _ _ _ _ _.
    Next Obligation.
      rewrite /cost. case (a i) => //. Qed.
    Next Obligation.
      apply smooth.
    Qed.

    Definition t := GameType bool mixin.
  End singletonGame_N.
End SingletonGame_N.        

Module BiasGame.
  Section biasGame.
    Local Open Scope ring_scope.

    Variable A : game.
    Variable c : rat.
    Definition N := (N A).
    Definition lambda := (lambda A).
    Definition mu := (mu A).

    Hypothesis c_pos : 0 <= c.
    Hypothesis lambda_mu_bound : 1 <= mu + lambda.

    Definition cost (n : 'I_N) (f : {ffun 'I_N -> A}) : rat := cost n f + c.
    Lemma smooth (a a' : {ffun 'I_N -> A}) :
        \sum_(i : 'I_N) cost i [ffun j => if i == j then a' i else a j] <=
        lambda * (\sum_(i < N) cost i a') + mu * (\sum_(i < N) cost i a).
    Proof.
      rewrite /cost !big_split.
      rat_to_ring.
      rewrite !mulrDr.
      rewrite -addrA.
      rewrite [lambda * _ + (mu * _ + _)] addrC.
      rewrite 2!addrA.
      rewrite -addrA.
      rewrite ler_add => //.
      apply smooth.
      rewrite !big_distrr -big_split. rat_to_ring.
      apply FunGame.leq_sum_rat.
      move => n _. rewrite -{1}[c] mulr1 -mulrDl {1}mulrC.
      apply ler_pmul => //.
    Qed.

    Program Definition mixin :=
      @NGame.Mixin A lambda mu N cost _ _ _ _ smooth.
    Next Obligation.
      rewrite /cost addr_ge0 => //.
      apply cost_pos. Qed.
    Next Obligation.
      apply lambda_pos. Qed.
    Next Obligation.
      apply mu_pos. Qed.
    Next Obligation.
      apply mu_lt1.
    Qed.

    Definition t := GameType A mixin.
  End biasGame.
End BiasGame.

Module AffineGame.
  Section affineGame.
    Variable a : rat.
    Variable b : rat.

    Hypothesis a_pos : 0 <= a.
    Hypothesis b_pos : 0 <= b.

    Variable g : game.
    Hypothesis lambda_mu_bound: 1 <= lambda g + mu g.
    Lemma lmb_pres : 1 <= lambda (ScalarGame.t g a_pos) + mu (ScalarGame.t g b_pos).
    Proof. auto. Qed.
 
    Definition t := @BiasGame.t (ScalarGame.t g a_pos) b b_pos lmb_pres.
  End affineGame.
End AffineGame.

Module ProdGame.
  Section prodGame.
    Local Open Scope ring_scope.

    Variable A B : game.

    Notation ty := ((A * B)%type).

    Definition cost (p1 p2 : ty) :=
      let: (a1, b1) := p1 in
      let: (a2, b2) := p2 in
      cost a1 a2 + cost b1 b2.

    Definition lambda := maxr (lambda A) (lambda B).
    Definition mu := maxr (mu A) (mu B).

    Lemma smooth (p1 p2 p1' p2' : ty) :
      cost p1' p2 + cost p2' p1 <=
      lambda * cost p1' p2' + lambda * cost p2' p1' +
      mu * cost p1 p2 + mu * cost p2 p1.
    Proof.
      case: p1=> a1 b1. case: p2=> a2 b2.
      case: p1'=> a1' b1'; case: p2'=> a2' b2'.
      rewrite /cost.
      have H: forall a b c d, a + c + (b + d) = a + b + c + d.
      { move=> X a b c d.
        by rewrite addrA -[(_ + c) + _]addrA [c + b]addrC addrA.
      }
      rewrite 4!mulrDr H -addrA.
      set La1 := lambda * _ a1' _.
      set Lb1 := lambda * _ b1' _.
      set La2 := lambda * _ a2' _.
      set Lb2 := lambda * _ b2' _.
      set Ma1 := mu * _ a1 _.
      set Mb1 := mu * _ b1 _.
      set Ma2 := mu * _ a2 _.
      set Mb2 := mu * _ b2 _.
      rewrite -[La1 + _ + _]addrA.
      rewrite [Lb1 + _]addrC.
      rewrite [La1 + _]addrA.
      rewrite [La1 + _]addrA.
      rewrite -[La1 + _ + _ + _]addrA.
      rewrite [Lb2 + _]addrC.
      rewrite -[La1 + _ + _ + _ + _]addrA.
      rewrite [Ma1 + _ + _]addrA.
      rewrite -[Ma1 + _ + _]addrA.
      rewrite [Mb1 + _]addrC.
      rewrite [Ma1 + _]addrA.
      rewrite -[Ma1 + _ + _ + _]addrA.
      rewrite -[La1 + _ + _ + _]addrA.
      rewrite [Lb1 + _ + _]addrA.
      rewrite [(Lb1 + _) + _]addrC.
      rewrite [(La1 + _) + (Ma1 + Ma2 + _ + _)]addrA.
      rewrite [La1 + _ + _]addrA.
      rewrite -[La1 + _ + _ + _ + _]addrA.
      apply: ler_add.
      {
      rewrite addrA.        
      move: (@smooth A a1 a2 a1' a2')=> H2.
      apply: ler_trans.
      apply: H2.
      rewrite /La1 /La2 /Ma1 /Ma2.
      apply: ler_add.
      apply: ler_add.
      apply: ler_add.
      rewrite /lambda.
      apply: ler_pmul=> //.
      by apply: lambda_pos.
      by apply: cost_pos.
      by rewrite ler_maxr; apply/orP; left.
      apply: ler_pmul=> //.
      by apply: lambda_pos.
      by apply: cost_pos.
      by rewrite ler_maxr; apply/orP; left.
      apply: ler_pmul=> //.
      by apply: mu_pos.
      by apply: cost_pos.
      by rewrite ler_maxr; apply/orP; left.
      apply: ler_pmul=> //.
      by apply: mu_pos.
      by apply: cost_pos.
      by rewrite ler_maxr; apply/orP; left.
      }
      rewrite addrA.      
      move: (@smooth B b1 b2 b1' b2')=> H2.
      apply: ler_trans.
      apply: H2.
      rewrite /Lb1 /Lb2 /Mb1 /Mb2.
      apply: ler_add.
      apply: ler_add.
      apply: ler_add.
      rewrite /lambda.
      apply: ler_pmul=> //.
      by apply: lambda_pos.
      by apply: cost_pos.
      by rewrite ler_maxr; apply/orP; right.
      apply: ler_pmul=> //.
      by apply: lambda_pos.
      by apply: cost_pos.
      by rewrite ler_maxr; apply/orP; right.
      apply: ler_pmul=> //.
      by apply: mu_pos.
      by apply: cost_pos.
      by rewrite ler_maxr; apply/orP; right.
      apply: ler_pmul=> //.
      by apply: mu_pos.
      by apply: cost_pos.
      by rewrite ler_maxr; apply/orP; right.
    Qed.

    Lemma cost_pos (p1 p2 : ty) : 0 <= cost p1 p2.
    Proof.
      case: p1=> ? ?; case: p2=> ? ?; rewrite /cost=> //.
      rewrite -[0]add0r.
      by apply: ler_add; apply: cost_pos.
    Qed.

    Lemma lambda_pos : 0 <= lambda.
    Proof.
      rewrite ler_maxr; apply/orP; left.
      apply: lambda_pos.
    Qed.      

    Lemma mu_pos : 0 <= mu.
    Proof.
      rewrite ler_maxr; apply/orP; left.
      apply: mu_pos.
    Qed.

    Lemma mu_lt1 : mu < 1.
    Proof.
      rewrite ltr_maxl.
      apply/andP; split; apply: mu_lt1.
    Qed.      
    
    Definition mixin :=
      @Game.Mixin ty cost lambda mu 
                  cost_pos lambda_pos mu_pos mu_lt1 smooth.
    Definition t := GameType ty mixin.
  End prodGame.
End ProdGame.
Canonical ProdGame.t.

Section prodGameTest.
  Variables A B : game.
  Variables (a : A) (b : B).
  Check cost (a, b) (a, b).
End prodGameTest.

(**
  Input:
    G : game - cost to be modified
    c : rat - the offset to apply
    f : G -> bool - a function that determines when to apply the offset 
  Ouput:
    t : a new game s.t. 
      G'.cost (p1, p2) = G.cost (p1, p2) + (if (f p1) then c else 0).
**)
Module OffsetGame.
  Section offsetGame.
    Local Open Scope rat_scope.

    Variable G : game.
    (**  f determines when to apply the offset.
        In the case of bool games (e.g. location
        and resource games), this should generally
        be the identity function **)
    Variable c : rat.
    Hypothesis c_pos : 0 <= c.
    Variable f : G -> bool.

    Definition rhGame := ScalarGame.t SingletonGame.t c_pos.
    Definition totalGame := ProdGame.t G rhGame.
    (** We want to consider the special case of
        the above totalGame when the singleton
        part is dependent on our move in the original
        game type
    **)
    Definition cost (a b : G) : rat :=
      @Game.cost totalGame (a, f a) (b, f b).

    Lemma cost_pos : forall a b, 0 <= cost a b.
    Proof. move => a b. apply ProdGame.cost_pos. Qed.
    Program Definition mixin :=
      @Game.Mixin G cost (lambda totalGame) (mu totalGame)
                  cost_pos (lambda_pos totalGame)
                  (mu_pos totalGame) (mu_lt1 totalGame) _.
      Next Obligation. apply ProdGame.smooth. Qed.
    Definition t := GameType G mixin.
  End offsetGame.
End OffsetGame.

Module FunGame.
  Section funGame.
    Local Open Scope ring_scope.
    
    Variable A : finType.
    Variable B : game.

    Definition ty := {ffun A -> B}.

    Definition cost (f g : ty) : rat :=
      \sum_(a : A) cost (f a) (g a).

    Definition lambda := (lambda B).
    Definition mu := (mu B).

    Lemma leq_sum_rat (I : finType) r (P : pred I) (E1 E2 : I -> rat):
      (forall i, P i -> E1 i <= E2 i) ->
        \sum_(i <- r | P i) (E1 i) <= \sum_(i <- r | P i) (E2 i).
    Proof. move=> leE12. elim/big_ind2: _ => // m1 m2 n1 n2. apply: ler_add.
    Qed.

    Lemma smooth (a b a' b' : ty) :
      cost a' b + cost b' a <=
      lambda * cost a' b' + lambda * cost b' a' +
      mu * cost a b + mu * cost b a.
    Proof.
      rewrite /cost.
      assert (
        \sum_a0 Game.Exports.cost (a' a0) (b a0)
          + \sum_a0 Game.Exports.cost (b' a0) (a a0)
        =
        \sum_a0 ((Game.Exports.cost (a' a0) (b a0))
                  +
                  (Game.Exports.cost (b' a0) (a a0)))).
      {
        rewrite -> big_split. simpl. reflexivity.
      }
      rewrite -> H. clear H.
      (* the goal here is to collect the sums on the
         rhs of the inequality to permit termwise comaprisons *)
      assert (lambda * (\sum_a0 Game.Exports.cost (a' a0) (b' a0)) +
                lambda * (\sum_a0 Game.Exports.cost (b' a0) (a' a0)) +
                mu * (\sum_a0 Game.Exports.cost (a a0) (b a0)) +
                mu * (\sum_a0 Game.Exports.cost (b a0) (a a0))
                  =
              \sum_a0 (lambda * Game.Exports.cost (a' a0) (b' a0) +
                       lambda * Game.Exports.cost (b' a0) (a' a0) +
                       mu * Game.Exports.cost (a a0) (b a0) +
                       mu * Game.Exports.cost (b a0) (a a0))).
      {
        replace (lambda * (\sum_a0 Game.Exports.cost (a' a0) (b' a0)))
          with ((\sum_a0 Game.Exports.cost (a' a0) (b' a0)) * lambda).
           Focus 2. apply mulqC.
        replace (lambda * \sum_a0 Game.Exports.cost (b' a0) (a' a0))
          with  ((\sum_a0 Game.Exports.cost (b' a0) (a' a0)) * lambda).
            Focus 2. apply mulqC.
        replace (mu * (\sum_a0 Game.Exports.cost (a a0) (b a0)))
          with ((\sum_a0 Game.Exports.cost (a a0) (b a0)) * mu).
            Focus 2. apply mulqC.
        replace (mu * (\sum_a0 Game.Exports.cost (b a0) (a a0)))
          with ((\sum_a0 Game.Exports.cost (b a0) (a a0)) * mu).
        Focus 2. apply mulqC.
        replace ((\sum_a0 Game.Exports.cost (a' a0) (b' a0)) * lambda +
                      (\sum_a0 Game.Exports.cost (b' a0) (a' a0)) * lambda)
        with (\sum_a0
               ((Game.Exports.cost (a' a0) (b' a0) * lambda) +
                (Game.Exports.cost (b' a0) (a' a0) * lambda))).
        Focus 2.
        set F := Game.Exports.cost.
        rewrite big_split /=.
        by rewrite -2!mulr_suml.
        rewrite <- addqA.
        replace ((((\sum_a0 Game.Exports.cost (a a0) (b a0)) * mu +
                 (\sum_a0 Game.Exports.cost (b a0) (a a0)) * mu)%Q)%Q)
          with (\sum_a0 ((Game.Exports.cost (a a0) (b a0)) * mu +
                   (Game.Exports.cost (b a0) (a a0)) * mu)).
        Focus 2. rewrite -> big_split. simpl.
        set F := Game.Exports.cost.
          by rewrite -2!mulr_suml.
        symmetry;  rewrite 3!big_split /=.
        symmetry. rewrite 2!big_split /=.
        rewrite -4!mulr_suml.
        rewrite -4!mulr_sumr.
        rewrite 2![lambda * _]mulrC 2![mu * _]mulrC.
          by rewrite -addrA.
      }
      rewrite -> H. clear H.
      assert (forall a0 : A,
              Game.Exports.cost (a' a0) (b a0) +
                Game.Exports.cost (b' a0) (a a0)
                  <=
              lambda * Game.Exports.cost (a' a0) (b' a0) +
               lambda * Game.Exports.cost (b' a0) (a' a0) +
               mu * Game.Exports.cost (a a0) (b a0) +
               mu * Game.Exports.cost (b a0) (a a0)).
      {
        intros a0.
        apply smooth.
      }
      apply leq_sum_rat. intros. apply H.
    Qed.

    Lemma cost_pos (p1 p2 : ty) : 0 <= cost p1 p2.
    Proof.      
      rewrite /cost. apply big_rec. auto.
      move => i n h1 h2. apply le_rat0D.
      apply cost_pos. auto.
    Qed.

    Lemma lambda_pos : 0 <= lambda.
    Proof.
      rewrite /lambda. apply lambda_pos.
    Qed.

    Lemma mu_pos : 0 <= mu.
    Proof.
      rewrite /mu. apply mu_pos.
    Qed.

    Lemma mu_lt1 : mu < 1.
    Proof.
      rewrite /mu. apply mu_lt1.
    Qed.      
    
    Definition mixin :=
      @Game.Mixin ty cost lambda mu 
                  cost_pos lambda_pos mu_pos mu_lt1 smooth.
    Definition t := GameType ty mixin.
  End funGame.
End FunGame.
Canonical FunGame.t.

(**
  The following module implements a two player congestion
    game with one resource and an affine cost functions.
**)
Module CongestionGame_2p1r.
  Section congestionGame_2p1r.
  Open Scope rat_scope.
    
    Variable mult_const : rat.
    Variable add_const : rat.
    Hypothesis mult_const_pos : 0 <= mult_const.
    Hypothesis add_const_pos :  0 <= add_const.
    
   (** first capture the multiplication **)
    Definition scalarResourceGame : game :=     
      ScalarGame.t ResourceGame.t mult_const_pos.
   (** set up the offset *)
    Definition t : game :=
      @OffsetGame.t scalarResourceGame add_const
         add_const_pos (fun g : bool => g).
      (* We use an identity function here because 
          our games are bools and we add the offset
          only if the player uses the resource *)
  End congestionGame_2p1r.
End CongestionGame_2p1r.
  
Section CG2p1r_test.
  Open Scope rat_scope.
  Theorem bleh : 0 <= 5%:R. by []. Qed.
  Eval compute in (
    (@Game.cost (CongestionGame_2p1r.t bleh bleh)) true true).
  Eval compute in (
    (@Game.cost (CongestionGame_2p1r.t bleh bleh)) true false).
  Eval compute in (
    (@Game.cost (CongestionGame_2p1r.t bleh bleh)) false false).
End CG2p1r_test.

(*Let's generalize to an arbitrary number of players
  for a single resource.

  We do this wi an application of our FunGame. Here, the functions
    f g : A -> bool denote a subset of players. In order
    to make sense in most contexts, f and g should partition A.
    
    Notably:
      \forall a : A, ~~ (f a || g a) ==> 
        it's the same game as if a never played.
    AND
      \forall a : A,  f a && g a ==> a is being double counted.

    It may even make sense to require f and g to partition A,
      but for the moment we can just make it general. 
*) 
Module CongestionGame_Np1r.
  Section congestionGame_Np1r.
  Open Scope rat_scope.
  Variable A : finType.
  
  Variables mult_const add_const : rat.
  Hypothesis mult_const_pos : 0 <= mult_const.
  Hypothesis add_const_pos : 0 <= add_const.

  Variable usingResource : A -> bool.

  Definition numUsingResource : rat := \sum_(a0 | usingResource a0) 1.
  Lemma prod_is_pos : 0 <= mult_const * numUsingResource.
    apply le_rat0M. by [].
    rewrite /numUsingResource.
    apply big_rec. by [].
    move => i x h1 h2.
    apply le_rat0D; by [].
  Qed.

  (** The cost accrued by each player per it's membership
      in the 'partitions' f g. Pretty much identical to
      the 2-player game in the section above **)
  Definition playerGame : game :=
    @OffsetGame.t (ScalarGame.t ResourceGame.t prod_is_pos) add_const
         add_const_pos (fun g : bool => g).

  Definition t : game :=
    FunGame.t A playerGame.
  End congestionGame_Np1r.
End CongestionGame_Np1r.

(* Let's generalize the above to
    an arbitrary number of resources *)
Module CongestionGame_2pNr.
  Section congestionGame_2pNr.
    (**
      - A is the (finite) type of resources
      - ty is a usage function that indicates if a player
        used resource a : A.
      - mult_const and add_const determine the respective
        parameters for the cost function associated with each
        resource
    **)
    Variable A : finType.

    Variable mult_const : A -> rat.
    Variable add_const : A -> rat.
    Hypothesis mult_const_pos : forall a : A, 0 <= mult_const a.
    Hypothesis add_const_pos : forall a : A, 0 <= add_const a.

    (**
       Now, at first I thought we wanted to
         use our FunGame here.
         BUT, (per my understanding) FunGame would 
         require us to play the same game for each resource.
         
       Since each resource has its own set of constants
        for its cost function, we need to pair these dudes up
    **)
    Definition costPerResource (a : A) := 
      CongestionGame_2p1r.t (mult_const_pos a) (add_const_pos a).

    Definition cprImage : seq game := image costPerResource A.
    
    (** Below, we chain together the games from cpaImage using ProdGame
        with EmptyGame as the base case 
        
        One thing I don't like here is the necessity for
        an 'empty game' and the fact that we have some sort of
        meaningless head in our n-tuple of bools. *)

    Definition t : game := foldl ProdGame.t UnitGame.t cprImage. 
  End congestionGame_2pNr.
End CongestionGame_2pNr. 

(** Let's combine techniques from 2pNr and Np1r
    to handle arbitrary congestion games **)
(**
  What I really want to do is to look at partitions
  of the set of players and talk about the cost f g
**)
Module CongestionGame.
  Section congestionGame.
    (* The type of players and resources, resp. *)
    Variables A B: finType.
    (* Constants for cost functions *)
    Variables mult_const add_const : B -> rat.
    Hypothesis mult_const_pos : forall b : B, 0 <= mult_const b.
    Hypothesis add_const_pos : forall b : B, 0 <= add_const b.

    Variable usingResource : B -> A -> bool.
    Definition numUsingResource (b : B) : rat
      := \sum_(a0 | usingResource b a0) 1.
    Lemma prod_is_pos :
      forall b : B, 0 <= (mult_const b) * (numUsingResource b).
    Proof.
      move => b. apply le_rat0M. by [].
      rewrite /numUsingResource.
      apply big_rec. by [].
      move => i x h1 h2.
      apply le_rat0D; by [].
    Qed.

    Definition costPerResource (b : B) : game :=
      @OffsetGame.t (ScalarGame.t ResourceGame.t (prod_is_pos b))
        (add_const b) (add_const_pos b) (fun g : bool => g).

    Definition cprImage : seq game := image costPerResource B.
    Definition prod_cprImage := foldl ProdGame.t UnitGame.t cprImage.
    
    Definition t : game := FunGame.t A prod_cprImage.
  End congestionGame.
End CongestionGame.

(** Equilibrium notions *)
Section gameDefs.
  Variable T : game.

  Notation "'state' T" := ((T*T)%type) (at level 80).

  (** We assume at least one state. *)
  Variable t0 : state T. 
  
  Definition switch (p : state T) : state T :=
    let: (s, o) := p in (o, s).
  
  (** [t] is a Pure Nash Equilibrium (PNE) when neither player is better off
      by moving to another strategy. *)
  Definition self_optimal (p : state T) : Prop :=
    let: (s, o) := p in
    forall s', cost s o <= cost s' o.
  Definition self_optimalb (p : state T) : bool :=
    let: (s, o) := p in
    [forall s', cost s o <= cost s' o].

  Definition PNE (p : state T) : Prop :=
    self_optimal p /\ self_optimal (switch p).

  (** PNE is decidable. *)
  Definition PNEb (p : state T) : bool :=
    [&& self_optimalb p & self_optimalb (switch p)].

  Lemma PNE_PNEb t : PNE t <-> PNEb t.
  Proof.
    case: t=> s o; split.
    { case=> H1 H2; apply/andP; split.
      apply/forallP=> s'; apply: H1.
      apply/forallP=> o'; apply: H2.
    }
    case/andP=> H1 H2; split.
    { move=> s'; apply: (forallP H1).
    }
    move=> o'; apply: (forallP H2).
  Qed.

  Lemma PNEP t : reflect (PNE t) (PNEb t).
  Proof.
    move: (PNE_PNEb t).
    case H: (PNEb t).
    { by move=> H2; constructor; rewrite H2.
    }
    move=> H2; constructor=> H3.
    suff: false by [].
    by rewrite -H2.
  Qed.

  Definition cost2 := [fun p : state T => cost p.1 p.2].
  
  (** The social Cost of a state is the sum of both players' costs. *)
  Definition Cost (t : state T) : rat := cost2 t + cost2 (switch t).

  (** A state is optimal if its social cost can't be improved. *)
  Definition optimal : pred (state T) :=
    fun t => [forall t0, Cost t <= Cost t0].

  (** The Price of Anarchy for game [T] is the ratio of WORST 
      equilibrium social cost to optimal social cost. We want to 
      ratio to be as close to 1 as possible. *)
  Definition PoA : rat :=
    Cost (arg_max PNEb Cost t0) / Cost (arg_min optimal Cost t0).

  (** The Price of Stability for game [T] is the ratio of BEST
      equilibrium social cost to optimal social cost. We want to 
      ratio to be as close to 1 as possible. *)
  Definition PoS : rat :=
    Cost (arg_min PNEb Cost t0) / Cost (arg_min optimal Cost t0).

  Lemma PoS_le_PoA (H : PNEb t0) (Hcost : forall t, Cost t > 0) : PoS <= PoA.
  Proof.
    rewrite /PoS /PoA.
    move: (min_le_max Cost H); rewrite /min /max=> H2.
    rewrite ler_pdivr_mulr.
    move: H2; move: (Cost _)=> x; move: (Cost _)=> y.
    have Hx: Cost (arg_min optimal Cost t0) != 0.
    { move: (Hcost (arg_min optimal Cost t0)); rewrite ltr_def.
      by case/andP=> H1 H2.
    }
    move: Hx; move: (Cost _)=> z Hx H2.
    have H3: (z = z / 1).
    { by rewrite (GRing.divr1 z).
    }
    rewrite {2}H3 mulf_div.
    rewrite GRing.mulr1.
    rewrite -GRing.mulrA.
    rewrite GRing.divff=> //.
    by rewrite GRing.mulr1.
    apply: Hcost.
  Qed.

  (** The expected cost to player [self] of a particular distribution
      over configurations.  Note that the distribution [d] need not
      be a product distribution -- in order to define Coarse
      Correlated Equilibria (below), we allow player distributions to
      be correlated with one another. *)
  Definition expCost
             (d : dist [finType of state T] [numDomainType of rat]) :=
    expectedValue d cost2.

  Definition ExpCost (d : dist [finType of state T] [numDomainType of rat]) :=
    expCost d +
    expectedValue d (cost2 \o switch).

  Lemma ExpCost_linear d :
    ExpCost d
    = expectedValue d (fun p => cost2 p + (cost2 \o switch) p). 
  Proof.
    rewrite /ExpCost /expCost /expectedValue /comp -big_split /=.
    by apply/congr_big=> // i _; rewrite -mulrDr.
  Qed.    

  Definition upd_self (s' : T) (t : state T) : state T := (s', t.2).
  Definition upd_other (o' : T) (t : state T) : state T := (t.1, o').      
  
  (** The expected cost of a self deviation *)
  Definition expUnilateralSelfCost
             (d : dist [finType of state T] [numDomainType of rat])
             (t' : state T) :=
    expectedValue d (cost2 \o upd_self t'.1). 

  (** The expected cost of an other deviation *)
  Definition expUnilateralOtherCost
             (d : dist [finType of state T] [numDomainType of rat])
             (t' : state T) :=
    expectedValue d (cost2 \o upd_self t'.2 \o switch). 

  Lemma expUnilateralCost_linear d t' :
    expUnilateralSelfCost d t' + expUnilateralOtherCost d t'
    = let: (s', o') := t' 
      in expectedValue
           d (fun t : state T =>
                let: (s, o) := t in 
                cost s' o + cost o' s). 
  Proof.
    rewrite /expUnilateralSelfCost /expUnilateralOtherCost /expectedValue.
    case: t'=> s' o' /=; rewrite -big_split /=; apply/congr_big=> // i _.
      by case: i=> s o; rewrite -mulrDr.
  Qed.      
  
  (** Coarse Correlated Equilibria 
      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state t' is
      greater or equal to the expected cost of distribution [d]. *)
  Definition CCE (d : dist [finType of state T] [numDomainType of rat]) : Prop :=
    forall t' : state T,
      expCost d <= expUnilateralSelfCost d t' /\
      expCost d <= expUnilateralOtherCost d t'.

  Definition CCEb (d : dist [finType of state T] [numDomainType of rat]) : bool :=
    [forall t' : state T,
      [&& expCost d <= expUnilateralSelfCost d t' 
        & expCost d <= expUnilateralOtherCost d t']].

  Lemma CCE_CCEb d : CCE d <-> CCEb d.
  Proof.
    split.
    { move=> H; apply/forallP=> t'; case: (H t')=> H1 H2.
        by apply/andP; split.
    }
    by move/forallP=> H t'; case: (andP (H t')).
  Qed.
    
  Lemma CCEP d : reflect (CCE d) (CCEb d).
  Proof.
    move: (CCE_CCEb d); case H: (CCEb d).
    { by move=> H2; constructor; rewrite H2.
    }
    by move=> H2; constructor; rewrite H2.
  Qed.

(*  (*Sketch of stuff for mult weights. Need some thought on
    how to express the 'randomness' of the function and
    definitions for regret *)
  Definition updateWeights
    (epsilon : rat)
    (strat : T)
    (selected_choice : T)
    (weights : {ffun T -> rat})
      : {ffun  T -> rat} :=
    weights.

  Fixpoint multWeights
    (epochs : nat)
    (epsilon : rat)
    (strat : {finType T})
    (** Currently, weights is not set up to be a distribution,
        but instead contains relative weights [0, 1]. **)
    (weights : {ffun [finType of T] -> rat})
    (** choice_fun takes as input some probabilty weighting, and
        'randomly' selects some state **) 
    (choiceFun : {ffun [finType of state T] -> rat} -> state T) :
    (** The output of the function is a new set of weights **)
    {ffun [finType of state T] -> rat}   :=
    match epochs with
    | O => weights
    | S n => multWeights n epsilon strat
              (updateWeights epsilon strat (choiceFun weights))
              choiceFun
    end.*)
End gameDefs.