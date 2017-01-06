Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Module PCM.
  Class t (A : Type) : Type :=
    mkMonoid {
        op : A -> A -> A;
        e : A;
        ind : A -> A -> Prop;
        assoc : forall a b c, op a (op b c) = op (op a b) c;
        idL : forall a, op e a = a;
        idR : forall a, op a e = a;
        com : forall a b, ind a b -> op a b = op b a
      }.
End PCM.

Infix "'oo'" := (PCM.op) (at level 50).
Notation "'ind'" := (PCM.ind) (at level 30).
Notation "'e'" := (PCM.e) (at level 30).

Section PCMLaws.
  Context {A} `(PCM.t A).
  Lemma pcm_assoc (a b c : A) : a 'oo' (b 'oo' c) = (a 'oo' b) 'oo' c.
  Proof. apply: PCM.assoc. Qed.
  Lemma pcm_idL (a : A) : e 'oo' a = a.
  Proof. apply: PCM.idL. Qed.                               
  Lemma pcm_idR (a : A) : a 'oo' e = a.
  Proof. apply: PCM.idR. Qed.
  Lemma pcm_com (a b : A) : ind a b -> a 'oo' b = b 'oo' a.
  Proof. apply: PCM.com. Qed.
End PCMLaws.  

Class Game (A : Type) `(M : PCM.t A) : Type :=
  mkGame {
      rules : A -> A -> Prop
    }.

Local Open Scope ring_scope.

Class Player (A : Type) `(G : Game A) (rty : realFieldType) : Type :=
  mkPlayer {
      cost : A -> rty;
      cost_ok : forall a : A, 0 <= cost a;
      strategy : A -> A -> Prop;
      strategy_ok :
        forall a rest : A, strategy rest a -> rules rest a
    }.

Section SmoothPlayer.
  Variable A : Type.
  Variable rty : realFieldType.
  Context `(G : Game A) (P : Player G rty).
  
  Class SmoothPlayer : Type :=
    mkSmoothPlayer {
        lambda : rty;
        mu : rty;
        smooth :
          forall rest other a : A,
            rules rest other ->
            strategy rest a -> 
            cost (a 'oo' rest) <=
            lambda * cost (other 'oo' a 'oo' rest) +  mu * (cost rest)
      }.
End SmoothPlayer.
  
Section TwoPlayerSmoothGame.
  Variable A : Type.
  Variable rty : realFieldType.
  Context `(G : Game A) (P1 P2 : Player G rty).
  Context (S1 : SmoothPlayer P1).
  Context (S2 : SmoothPlayer P2).  
  
  Inductive step : nat -> A -> nat -> A -> Prop :=  
  | step_even :
      forall a rest n,
        PeanoNat.Nat.Even n ->
        strategy (Player:=P1) rest a -> 
        step n rest (S n) (a 'oo' rest)
  | step_odd :
      forall b rest n,
        PeanoNat.Nat.Odd n ->
        strategy (Player:=P2) rest b ->         
        step n rest (S n) (b 'oo' rest).
  
  Lemma smooth_aux (a b rest : A) :
    ind a b ->
    strategy (Player:=P1) rest a ->
    strategy (Player:=P2) rest b ->     
    exists lambda mu,
      cost (Player:=P1) (a 'oo' rest) + cost (Player:=P2) (b 'oo' rest) <=
      lambda * (cost (Player:=P1) (b 'oo' a 'oo' rest)) +
      lambda * (cost (Player:=P2) (a 'oo' b 'oo' rest)) +   
      mu * (cost (Player:=P1) rest) + 
      mu * (cost (Player:=P2) rest).
  Proof.
    move=> H X1 X2.
    have R1: rules rest a by apply: (strategy_ok X1).
    have R2: rules rest b by apply: (strategy_ok X2).
    generalize (smooth R2 X1)=> Y1.
    generalize (smooth R1 X2)=> Y2.
    rewrite -(pcm_com H) in Y1.
    exists (Num.max (lambda (P:=P1)) (lambda (P:=P2))).
    exists (Num.max (mu (P:=P1)) (mu (P:=P2))).
    rewrite -(pcm_com H).
    move: Y1 Y2.
    set x := (Num.max _ _ * _).
    set y := (Num.max _ _ * _).
    set z := (Num.max _ _ * _).
    set w := (Num.max _ _ * _).
    set u := cost (a 'oo' _).
    set v := cost (b 'oo' _).
    move=> Y1 Y2.
    suff: u + v <= (x + z) + (y + w)
      by rewrite -addrA [z + _]addrA [z + _]addrC 2!addrA.
    apply: ler_add.
    { rewrite /x /z; eapply ler_trans. eapply Y1.
      apply: ler_add.
      { rewrite maxr_pmull; first by rewrite ler_maxr; apply/orP; left.
        by apply: cost_ok.
      }
      rewrite maxr_pmull; first by rewrite ler_maxr; apply/orP; left.
      by apply: cost_ok.
    }
    { rewrite /y /w; eapply ler_trans. eapply Y2.
      apply: ler_add.
      { rewrite maxr_pmull; first by rewrite ler_maxr; apply/orP; right.
        by apply: cost_ok.
      }
      rewrite maxr_pmull; first by rewrite ler_maxr; apply/orP; right.
      by apply: cost_ok.
    }
  Qed.

  (** prove more stuff here about the particular step dynamics 
      given above... *)
End TwoPlayerSmoothGame.
  
        

      
                                    
