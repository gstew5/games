Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

(** This file defines generic notions of extrema. *)

Section Extrema.
(** The primary parameters are:
      - [rty : realFieldType]    A real field
      - [I : finType]            A finite type
      - [P : pred I]             A subset of [I] 
      - [F : I -> rty]           A "valuation" function over [I] 
    The module implements the following functions: 
      - [arg_min]                An [i : I \in P] that minimizes [F]
      - [arg_max]                An [i : I \in P] that maximizes [F]
      - [min]                    := [F arg_min]
      - [max]                    := [F arg_max]
*)
  Variable rty : realFieldType.
  Variables (I : finType) (P : pred I) (F : I -> rty).

  Section getOrd.
    Variable ord : rel rty.
    Hypothesis ord_refl : reflexive ord.
    Hypothesis ord_trans : transitive ord.
    Hypothesis ord_total : total ord.

    Fixpoint getOrd (i0 : I) (l : list I) : I :=
      if l is (i :: l') then
        if ord (F i0) (F i) then getOrd i0 l' else getOrd i l'
      else i0.

    Lemma getOrd_mono i1 i2 l :
      ord (F i1) (F i2) ->
      ord (F (getOrd i1 l)) (F (getOrd i2 l)).
    Proof.
      move: i1 i2; elim: l=> // a l IH i1 i2 H /=.
      case H2: (ord (F i1) (F a)). 
      { by case H3: (ord (F i2) (F a)); apply: IH.
      }
      case H3: (ord (F i2) _)=> //.
      apply: IH.
      have H4: ord (F i1) (F a).
      { by apply: ord_trans; first by apply: H.
      }
      by rewrite H4 in H2.
    Qed.    

    Lemma getOrd_minimalIn i0 l :
      [&& ord (F (getOrd i0 l)) (F i0)
        & [forall (t | t \in l), ord (F (getOrd i0 l)) (F t)]].
    Proof.
      move: i0; elim: l.
      { move=> i0; apply/andP; split=> //.
        by apply/forallP.
      }
      move=> a l IH i0.
      apply/andP; split.
      { simpl; case H2: (ord (F i0) _)=> //.
        by case: (andP (IH i0)).                                        
        apply: ord_trans.        
        case: (andP (IH a))=> H3 _; apply: H3.
        by case: (orP (ord_total (F i0) (F a))); first by rewrite H2.
      }
      apply/forallP=> x; apply/implyP.
      move: (in_cons a l x)=> ->; case/orP.
      { move/eqP=> ?; subst x=> /=.
        case H4: (ord (F i0) _).
        case: (andP (IH i0))=> H2 _.
        by apply: ord_trans; first by apply: H2.
        by case: (andP (IH a)).
      }
      move=> H /=.
      case H2: (ord (F i0) _).
      { case: (andP (IH i0))=> H0; move/forallP; move/(_ x).
        by move/implyP; move/(_ H)=> H3.
      }
      case: (andP (IH a))=> H3; move/forallP; move/(_ x).
      by move/implyP; move/(_ H)=> H4.
    Qed.

    Definition getOrd_tot i0 := getOrd i0 (enum I).
    
    Lemma getOrd_totP i0 : [forall i, ord (F (getOrd_tot i0)) (F i)].
    Proof.
      case: (andP (getOrd_minimalIn i0 (enum I)))=> H H2.
      apply/forallP=> x; apply/implyP=> H3.
      suff H4: false by [].
      apply: H3; move: (forallP H2 x); move/implyP; apply.
      by rewrite mem_enum.
    Qed.

    Definition getOrd_sub i0 := getOrd i0 (filter P (enum I)).

    Lemma getOrd_sub_hasP i0 (Hi0 : P i0) : P (getOrd_sub i0).
    Proof.
      rewrite /getOrd_sub; move: (enum I)=> l.
      elim: l=> // a l /=.
      case H: (P a)=> //=.                   
      case: (ord _ _)=> //.                      
      elim: l a H i0 Hi0 => //= a0 l IH a H i0 Hi0.
      case H2: (P a0)=> //=.
      case: (ord _ _).
      case: (ord _ _)=> //.
      by apply: IH.
      by apply: IH.
      case: (ord _ _)=> //.
      by apply: IH.
      by apply: IH.
    Qed.        
      
    Lemma getOrd_subP i0 (Hi0 : P i0) :
      [&& P (getOrd_sub i0)
        & [forall (i | P i), ord (F (getOrd_sub i0)) (F i)]].
    Proof.
      case: (andP (getOrd_minimalIn i0 (filter P (enum I))))=> H H2.
      apply/andP; split; first by apply: getOrd_sub_hasP.
      apply/forallP=> x; apply/implyP=> H3.
      move: (forallP H2 x); move/implyP; apply.
      by rewrite mem_filter; apply/andP; split=> //; rewrite mem_enum.
    Qed.
  End getOrd.

  Section default.
    Variable i0 : I.
    Hypothesis H : P i0.
  
    Definition arg_max := getOrd_sub ger i0.
  
    Lemma arg_maxP : [&& P arg_max & [forall (i | P i), F arg_max >= F i]].
    Proof.
      apply: getOrd_subP=> //; rewrite /ger.
      by apply: lerr.
      by move=> x y z /= H2 H3; apply: (ler_trans H3 H2).
      by move=> x y /=; move: (ler_total x y); rewrite orbC.
    Qed.

    Definition max := F arg_max.

    Lemma maxP : [forall (i | P i), max >= F i].
    Proof.
      rewrite /max.
      by case: (andP arg_maxP).
    Qed.      
    
    Definition arg_min := getOrd_sub ler i0.

    Lemma arg_minP : [&& P arg_min & [forall (i | P i), F arg_min <= F i]].
    Proof.
      apply: getOrd_subP=> //.
      by apply: ler_trans.                           
      by apply: ler_total.
    Qed.

    Definition min := F arg_min.

    Lemma minP : [forall (i | P i), min <= F i].
    Proof.
      rewrite /min.
      by case: (andP arg_minP).
    Qed.      
  
    Lemma min_le_max : min <= max.
    Proof.
      rewrite /min /max.
      case: (andP arg_minP)=> H2; move/forallP=> H3.
      case: (andP arg_maxP)=> H4; move/forallP=> H5.
      move: (implyP (H3 i0)); move/(_ H)=> Hx.
      move: (implyP (H5 i0)); move/(_ H)=> Hy.
      apply: ler_trans.
      apply: Hx.
      apply: Hy.
    Qed.
  End default.
End Extrema.

Arguments arg_min [rty I] P F i0.
Arguments arg_max [rty I] P F i0.

Arguments arg_minP [rty I P] F [i0] _.
Arguments arg_maxP [rty I P] F [i0] _.

Arguments min [rty I] P F i0.
Arguments max [rty I] P F i0.

Arguments minP [rty I P] F [i0] _.
Arguments maxP [rty I P] F [i0] _.

Arguments min_le_max [rty I P] F [i0] _.

Lemma max_ge (rty : realFieldType) (I : finType) (f : I -> rty) (def i : I) :
  f i <= max xpredT f def.
Proof.
  have H: xpredT i by [].
  move: (forallP (@maxP rty I xpredT f def H)); move/(_ i).
  by move/implyP; apply.
Qed.

Lemma min_le (rty : realFieldType) (I : finType) (f : I -> rty) (def i : I) :
  min xpredT f def <= f i.
Proof.
  have H: xpredT i by [].
  move: (forallP (@minP rty I xpredT f def H)); move/(_ i).
  by move/implyP; apply.
Qed.
