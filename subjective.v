Set Implicit Arguments.
Unset Strict Implicit.

Require Import pcm.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema dist.

Local Open Scope ring_scope.

Lemma subsetI_iff (T : finType) (X Y : {set T}) :
  X \subset Y <-> (forall x, x \in X -> x \in Y).
Proof.
  split; first by move/subsetP=> H x; apply: (H x).
  by move=> H; apply/subsetP=> x; apply: (H x).
Qed.

Lemma subsetI (T : finType) (X Y : {set T}) :
  reflect (forall x, x \in X -> x \in Y) (X \subset Y).
Proof.
  apply/subsetP.
Qed.

(** This module defines an interface over smooth subjective games. *)

Module Game.
  Section ClassDef.
    Record mixin_of T :=
      Mixin { mx_cost : T -> T -> rat;
              mx_lambda : rat;
              mx_mu : rat;
              mx_cost_pos :
                forall a b : T, 0 <= mx_cost a b;
              mx_lambda_pos : 0 <= mx_lambda;
              mx_mu_pos : 0 <= mx_mu;              
              mx_mu_lt1 : mx_mu < 1;
              mx_smooth :
                forall a b a' b' : T,
                  mx_cost a' b + mx_cost b' a <=
                  mx_lambda * (mx_cost a' b') +
                  mx_lambda * (mx_cost b' a') +                  
                  mx_mu * (mx_cost a b) +
                  mx_mu * (mx_cost b a)                  
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
    
    Definition cost := @mx_cost _ (mixin class).
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
      Definition cost : T -> T -> rat := @cost T.
      Definition lambda : rat := @lambda T.
      Definition mu : rat := @mu T.
      Lemma cost_pos (a b : T) : 0 <= cost a b.
      Proof. by apply: (mx_cost_pos (mixin (class T))). Qed.
      Lemma lambda_pos : 0 <= lambda.
      Proof. by apply: (mx_lambda_pos (mixin (class T))). Qed.
      Lemma mu_pos : 0 <= mu.
      Proof. by apply: (mx_mu_pos (mixin (class T))). Qed.
      Lemma mu_lt1 : mu < 1.
      Proof. by apply: (mx_mu_lt1 (mixin (class T))). Qed.
      Lemma smooth (a b a' b' : T) : 
        cost a' b + cost b' a <=
        lambda * cost a' b' + lambda * cost b' a' +
        mu * cost a b + mu * cost b a.                                        
      Proof. by apply: (mx_smooth (mixin (class T))). Qed.
    End defs.
    Arguments cost [T] _ _.
    Arguments lambda _.
    Arguments mu _.
    Arguments cost_pos [_] _ _.
    Arguments lambda_pos _.
    Arguments mu_lt1 _.
    Arguments smooth [_ _ _ _ _].
  End Exports.
End Game.
Export Game.Exports.

(** Two-player, one-resource games *)

Module ResourceGame.  
  Section resourceGame.
    Local Open Scope rat_scope.
    
    Definition cost (a b : bool) : rat :=
      match a, b with
      | false, false => 0
      | false, true => 0
      | true, false => 1
      | true, true => 2%:R
      end.
    
    Program Definition mixin :=
      @Game.Mixin bool cost (5%:Q/3%:Q) (1%:Q/3%:Q) _ _ _ _ _.
    Next Obligation. case: a; case: b=> //. Qed.
    Next Obligation. case: a'; case: b'; case: a; case: b=> //. Qed.
    Definition t := GameType bool mixin.
  End resourceGame.
End ResourceGame.

(** Two-player, one-location games *)

Module LocationGame.
  Section locationGame.
    Local Open Scope rat_scope.
    
    Definition cost (a b : bool) : rat :=
      match a, b with
      | false, false => 1
      | false, true => 0
      | true, false => 1
      | true, true => 1
      end.
    
    Program Definition mixin :=
      @Game.Mixin bool cost 2%:R 0 _ _ _ _ _.
    Next Obligation. case: a; case: b=> //. Qed.
    Next Obligation. case Ha': a'; case Hb': b'; case Ha: a; case Hb: b=> //=. Qed.
    Definition t := GameType bool mixin.
  End locationGame.
End LocationGame.

(** [C(a, b) = c * C(a, b)], for some positive rational [c] *)

Module ScalarGame.
  Section scalarGame.
    Local Open Scope ring_scope.
    
    Variable A : game.
    Variable c : rat.
    Hypothesis c_pos : 0 <= c.

    Definition cost (a b : A) := c * cost a b.
      
    Definition lambda := lambda A.
    Definition mu := mu A.
    
    Lemma smooth (a b a' b' : A) :
      cost a' b + cost b' a <=
      lambda * cost a' b' + lambda * cost b' a' +
      mu * cost a b + mu * cost b a.
    Proof.
      rewrite /cost !mulrA [lambda * c]mulrC [mu * c]mulrC -!mulrA -!mulrDr.
      apply: ler_pmul=> //.
      apply: addr_ge0; apply: cost_pos.
        by rewrite mulrDr; apply: smooth.
    Qed.
    
    Lemma cost_pos (a b : A) : 0 <= cost a b.
    Proof. rewrite /cost; apply: mulr_ge0=> //; apply: cost_pos. Qed.

    Lemma lambda_pos : 0 <= lambda.
    Proof. apply: lambda_pos. Qed.      

    Lemma mu_pos : 0 <= mu.
    Proof. apply: mu_pos. Qed.

    Lemma mu_lt1 : mu < 1.
    Proof. apply: mu_lt1. Qed.      
    
    Definition mixin :=
      @Game.Mixin A cost lambda mu 
                  cost_pos lambda_pos mu_pos mu_lt1 smooth.
    Definition t := GameType A mixin.
  End scalarGame.
End ScalarGame.  

(** The unit game, with [C(a, b) = 0] for all [a, b] *)

Module UnitGame.
  Section unitGame.
    Local Open Scope ring_scope.

    Definition cost (a b : unit) : rat := 0.
    Program Definition mixin :=
      @Game.Mixin unit cost 0 0 _ _ _ _ _.
    Definition t := GameType unit mixin.
  End unitGame.
End UnitGame.

(* 
  The purpose of this silly singleton game is to 
  avoid needing to specify a specific offset game for bools
*)
Module SingletonGame.
  Section singletonGame.
    Local Open Scope ring_scope.

    Definition cost (a b : bool) : rat :=
      match a with
      | true => 1
      | false => 0
      end.

    Program Definition mixin :=
      @Game.Mixin bool cost 1%:R 0 _ _ _ _ _.
    Next Obligation. case: a; case: b=> //. Qed.
    Next Obligation. case Ha': a'; case Hb': b'; case Ha: a; case Hb: b=> //=. Qed.
    Definition t := GameType bool mixin.
  End singletonGame.
End SingletonGame.        

Module BiasGame.
  Section biasGame.
    Local Open Scope ring_scope.

    Variable A : game.
    Variable c : rat.
    Hypothesis c_pos : 0 <= c.

    Definition cost (a b : A) : rat := cost a b + c.

    Hypothesis lambda_mu_bound : (lambda A) + (mu A) >= 1%:Q.
    
    Notation lambda := (lambda A).
    Notation mu := (mu A).

    Lemma smooth (a b a' b' : A) :
      cost a' b + cost b' a <=
      lambda * cost a' b' + lambda * cost b' a' +
      mu * cost a b + mu * cost b a.
    Proof.
      rewrite /cost.
      set F := Game.Exports.cost.
      rewrite addrA.
      rewrite -[_ + c + _] addrC addrA.
      rewrite ![_ * _] mulqC .
      rewrite !mulq_addl.
      rewrite !addrA.
      have H: F A b' a + F A a' b + c + c = (F A a' b + F A b' a) + (c + c).
      {
        rewrite [F A a' b + F A b' a] addrC.
        rewrite -!addrA. auto.
      }
      rewrite H; move {H}.
      have H: forall (a b c d e f g h : rat),
        a + b + c + d + e + f + g + h = (a + c + e + g) + ((b + f) + (d + h)).
      {
        move => x1 x2 x3 x4 y1 y2 y3 y4.
        rewrite -!addrA.
        rewrite [x2 + _] addrC.
        rewrite [x4 + _] addrC.
        rewrite [y2 + _] addrC.
        rewrite -[y3 + _ + _] addrA.
        rewrite -[_ + x2] addrA.
        rewrite [ y4 + y2] addrC.
        rewrite [x2 + _] addrC.
        rewrite [x4 + _] addrC.
        rewrite !addrA. auto.
      }
      rewrite -> H.
      clear H.
      have H1:
        F A a' b + F A b' a <=
          (F A a' b' * lambda) + (F A b' a' * lambda) +
          (F A a b * mu) + (F A b a * mu).
      {
        rewrite ![ _ * lambda ] mulrC.
        rewrite ![ _ * mu ] mulrC.
        apply smooth.
      }
      have H2:
        c + c <= ((c * lambda) + (c * mu)) + ((c * lambda) + (c * mu)).
      {
        apply ler_add;
        rewrite ![c * _] mulrC;
        ring_to_rat;
        rewrite -mulq_addl;
        rat_to_ring;
        apply ler_pemull=> //.
      }
      apply ler_add.
      apply: H1.
      apply: H2.
    Qed.

    Lemma cost_pos (a b : A) : 0 <= cost a b.
    Proof.
      rewrite /cost.
      apply ler_paddr.
      auto.
      apply cost_pos.
    Qed.

    Lemma lambda_pos : 0 <= lambda.
    Proof.
      apply lambda_pos.
    Qed.
    Lemma mu_pos : 0 <= mu.
    Proof.
      apply mu_pos.
    Qed.
    Lemma mu_lt1 : mu < 1.
    Proof.
      apply mu_lt1.
    Qed.
    
    Definition mixin :=
      @Game.Mixin A cost lambda mu 
                  cost_pos lambda_pos mu_pos mu_lt1 smooth.
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

Module FGame.
  Section fGame.
    Local Open Scope ring_scope.

    Variable A : game.

    Variable f : A -> A -> rat.

    Definition cost (a b : A) := cost a b + f a b.

    Hypothesis f_smooth :
      forall a b a' b',
        f a' b + f b' a <=
        lambda A * f a' b' + lambda A * f b' a' +
        mu A * f a b + mu A * f b a.

    Hypothesis cost_pos :
      forall a b, 0 <= cost a b.

    Definition lambda := lambda A.
    Definition mu := mu A.

    Lemma smooth (a b a' b' : A) :
      cost a' b + cost b' a <=
      lambda * cost a' b' + lambda * cost b' a' +
      mu * cost a b + mu * cost b a.
    Proof.
      rewrite /cost.
      rewrite -addrA [f a' b + _]addrC 2!addrA.
      rewrite -[(_ + f b' a) + _]addrA.
      rewrite 4!mulrDr.
      rewrite [lambda * _ + _ + _]addrA.
      rewrite -[lambda * _ + _ + _]addrA.
      rewrite [lambda * f a' b' + _]addrC.
      rewrite [lambda * _ + (lambda * _ + lambda * f a' b')]addrA.
      rewrite -[_ + (mu * _ + _)]addrA.
      rewrite -[_ + (mu * _ + _)]addrA.
      rewrite [mu * f a b + _]addrC.
      rewrite [mu * _ + (mu * _ + _ + _)]addrA.
      rewrite [mu * _ + (_ + _)]addrA.
      rewrite -[(mu * _ + _ + _) + _]addrA.
      rewrite [mu * f b a + _]addrC.
      rewrite -[(lambda * _ + _ + _) + _]addrA.
      rewrite -[(_ + (lambda * _ + _)) + _]addrA.
      rewrite [(lambda * _ + _ + (mu * _ + _ + _))]addrA.
      rewrite [(lambda * _ + _) + (mu * _ + mu * _)]addrC.
      rewrite 2![(lambda * _ + lambda * _) + _]addrA.
      rewrite [(lambda * _ + _) + _]addrA.
      rewrite -[(_ + (lambda * f a' b' + _)) + _]addrA. 
      apply: ler_add; first by apply: smooth.
      by rewrite addrA addrC; apply: f_smooth.
    Qed.
    
    Lemma lambda_pos : 0 <= lambda.
    Proof. by apply: lambda_pos. Qed.      
    Lemma mu_pos : 0 <= mu.
    Proof. by apply: mu_pos. Qed.
    Lemma mu_lt1 : mu < 1.
    Proof. by apply: mu_lt1. Qed.
    
    Definition mixin :=
      @Game.Mixin A cost lambda mu 
                  cost_pos lambda_pos mu_pos mu_lt1 smooth.
    Definition t := GameType A mixin.
  End fGame.
End FGame.

Module SubGame.
  Section subGame.
    Local Open Scope ring_scope.

    Variable A : game.

    Variable f : A -> A -> rat.

    Let subf := [fun a b => - f a b].
    
    Hypothesis subf_smooth :
      forall a b a' b',
        subf a' b + subf b' a <=
        lambda A * subf a' b' + lambda A * subf b' a' +
        mu A * subf a b + mu A * subf b a.

    Hypothesis cost_subf_pos :
      forall a b, 0 <= cost a b + subf a b.
    
    Definition t := FGame.t subf_smooth cost_subf_pos.
  End subGame.
End SubGame.

(** 
  Sigma Games
  ~~~~~~~~~~~

  Input: 
    A : game
    p : pred A

  Output:
    t : a new game over type {a : A | p a} s.t. 
    cost x y = cost A x.1 y.1
**)

Module SigGame.
  Section sigGame.
    Local Open Scope ring_scope.

    Variable A : game.

    Variable p : pred A.

    Notation ty := ({a : A | p a}). 

    Definition cost (p1 p2 : ty) := cost (projT1 p1) (projT1 p2).

    Lemma smooth (p1 p2 p1' p2' : ty) :
      cost p1' p2 + cost p2' p1 <=
      lambda A * cost p1' p2' + lambda A * cost p2' p1' +
      mu A * cost p1 p2 + mu A * cost p2 p1.
    Proof.
      case: p1=> a1 b1. case: p2=> a2 b2.
      case: p1'=> a1' b1'; case: p2'=> a2' b2'.
      rewrite /cost /=.
      apply: smooth.
    Qed.      

    Lemma cost_pos (p1 p2 : ty) : 0 <= cost p1 p2.
    Proof.
      case: p1=> ? ?; case: p2=> ? ?.
      rewrite /cost=> //=; apply: cost_pos.
    Qed.
    Lemma lambda_pos : 0 <= lambda A.
    Proof. apply: lambda_pos. Qed.      
    Lemma mu_pos : 0 <= mu A.
    Proof. apply: mu_pos. Qed.
    Lemma mu_lt1 : mu A < 1.
    Proof. apply: mu_lt1. Qed.      
    
    Definition mixin :=
      @Game.Mixin ty cost (lambda A) (mu A)
                  cost_pos lambda_pos mu_pos mu_lt1 smooth.
    Definition t := GameType ty mixin.
  End sigGame.
End SigGame.
Canonical SigGame.t.

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
      For each player self and other, the expected cost of a
      unilateral deviation to state t' is greater or equal to the
      expected cost of distribution [d]. *)
  Definition CCE (d : dist [finType of state T] [numDomainType of rat]) : Prop :=
    forall t' : state T,
      expCost d <= expUnilateralSelfCost d t' /\
      expectedValue d (cost2 \o switch) <= expUnilateralOtherCost d t'.

  Definition CCEb (d : dist [finType of state T] [numDomainType of rat]) : bool :=
    [forall t' : state T,
      [&& expCost d <= expUnilateralSelfCost d t' 
        & expectedValue d (cost2 \o switch) <= expUnilateralOtherCost d t']].

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
End gameDefs.