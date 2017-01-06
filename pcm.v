Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema dist.

(** This module defines an interface over partial commutative monoids. *)

Module PCM.
  Section ClassDef. 
    Record mixin_of T :=
      Mixin { mx_op  : T -> T -> T;
              mx_dom : rel T;
              mx_e   : T;

              mx_opA :
                forall a b c,
                  mx_dom a b ->
                  mx_dom (mx_op a b) c ->
                  mx_dom b c ->
                  mx_dom a (mx_op b c) -> 
                  mx_op (mx_op a b) c = mx_op a (mx_op b c);
              mx_opC :
                forall a b,
                  mx_dom a b -> 
                  mx_op a b = mx_op b a;

              mx_domC :
                forall a b, mx_dom a b = mx_dom b a;
              mx_edom : forall a, mx_dom mx_e a;
              
              mx_eUL : forall a, mx_op mx_e a = a;
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
    
    Definition op := mx_op (mixin class).
    Definition dom := mx_dom (mixin class).    
    Definition e := mx_e (mixin class).
  End ClassDef.

  Module Import Exports.
    Coercion base : class_of >-> Finite.class_of.
    Coercion sort : type >-> Sortclass.
    Coercion eqType : type >-> Equality.type.
    Coercion finType : type >-> Finite.type.
    Canonical eqType.
    Canonical finType.
    Notation pcm := type.
    Notation pcmMixin := mixin_of.
    Notation PcmType T m := (@pack T m _ _ id).
    Notation "[ 'pcm' 'of' T 'for' cT ]" :=
      (@clone T cT _ idfun)
        (at level 0, format "[ 'pcm'  'of'  T  'for'  cT ]") : form_scope.
    Notation "[ 'pcm' 'of' T ]" :=
      (@clone T _ _ id)
        (at level 0, format "[ 'pcm'  'of'  T ]") : form_scope.

    Section defs.
      Variable T : pcm.
      Definition op : T -> T -> T := @op T.
      Definition dom : rel T := @dom T.
      Definition e : T := @e T.
      Lemma opA (a b c : T) :
        dom a b -> dom (op a b) c -> dom b c -> dom a (op b c) ->
        op (op a b) c = op a (op b c).
      Proof. by apply: (@mx_opA _ (mixin (class T))). Qed.
      Lemma opC (a b : T) : dom a b -> op a b = op b a.
      Proof. by apply: (@mx_opC _ (mixin (class T))). Qed.
      Lemma domC (a b : T) : dom a b = dom b a.
      Proof. by apply: (@mx_domC _ (mixin (class T))). Qed.
      Lemma edom (a : T) : dom e a.
      Proof. by apply: (@mx_edom _ (mixin (class T))). Qed.
      Lemma opeUL (a : T) : op e a = a.
      Proof. by apply: (@mx_eUL _ (mixin (class T))). Qed.
      Lemma opeUR (a : T) : op a e = a.
      Proof.
        rewrite opC.
        by apply: (@mx_eUL _ (mixin (class T))).
        by rewrite domC; apply: edom.
      Qed.
    End defs.              
  End Exports.
End PCM.
Export PCM.Exports.

Module BoolPCM.
  Definition dom a b := if a then ~~b else true.
  Program Definition mixin :=
    @PCM.Mixin bool orb dom false _ _ _ _ _.
  Next Obligation. by rewrite orbA. Qed.
  Next Obligation. by rewrite orbC. Qed.
  Next Obligation. by case: a=> //; case: b. Qed.
  Definition t := PcmType bool mixin.
End BoolPCM.
Canonical BoolPCM.t.

Module ProdPCM.
  Section prodPCM.
    Variables A B : pcm.
    
    Definition dom (p1 p2 : A * B)  :=
      let: (a1, b1) := p1 in
      let: (a2, b2) := p2 in
      [&& dom a1 a2 & dom b1 b2].

    Definition op (p1 p2 : A * B) := 
      let: (a1, b1) := p1 in
      let: (a2, b2) := p2 in
      (op a1 a2, op b1 b2).

    Lemma opA p1 p2 p3 :
      dom p1 p2 ->
      dom (op p1 p2) p3 ->
      dom p2 p3 ->
      dom p1 (op p2 p3) ->
      op (op p1 p2) p3 = op p1 (op p2 p3).
    Proof.
      case: p1=> a1 b1; case: p2=> a2 b2; case: p3=> a3 b3 /=.
      case/andP=> H0 H; case/andP=> H1 H2; case/andP=> H3 H4; case/andP=> H5 H6.
      f_equal.
      apply opA=> //.
      apply opA=> //.
    Qed.

    Lemma opC p1 p2 :
      dom p1 p2 -> op p1 p2 = op p2 p1.
    Proof.
      case: p1=> a1 b1; case: p2=> a2 b2=> /=.
      case/andP=> H0 H; f_equal; apply: opC=> //.
    Qed.

    Lemma domC p1 p2 : dom p1 p2 = dom p2 p1.
    Proof.
      case: p1=> a1 b1; case: p2=> a2 b2=> /=.
      f_equal; apply: domC.
    Qed.

    Definition e := (e A, e B).
    
    Lemma edom p : dom e p.
    Proof.
      case: p=> a b; apply/andP; split; apply: edom.
    Qed.

    Lemma eUL p : op e p = p.
    Proof.
      case: p=> a b; simpl; f_equal; apply opeUL.
    Qed.      
    
    Definition mixin := @PCM.Mixin (A*B) op dom e opA opC domC edom eUL.
    Definition t := PcmType (A*B) mixin.
  End prodPCM.
End ProdPCM.
Canonical ProdPCM.t.

Module HeapPCM.
  Section heapPCM.
    Variable val : finType.
    Variable vundef : val.
    Variable size : nat.
    Definition loc := 'I_size.
    Definition heap := {ffun loc -> val}.
    Definition dom : rel heap :=
      fun a b => [forall l : loc, (a l == vundef) || (b l == vundef)].
    Definition e : heap := finfun (fun _ => vundef).

    Definition join (v1 v2 : val) : val :=
      if v1 == vundef then v2
      else if v2 == vundef then v1
           else vundef.
    
    Definition op (a b : heap) : heap :=
      finfun (fun l : loc => join (a l) (b l)).
                
    Lemma opA a b c :
      dom a b -> dom (op a b) c -> dom b c -> dom a (op b c) ->
      op (op a b) c = op a (op b c).
    Proof.
      move=> H1 H2 H3 H4.
      rewrite /op -ffunP=> l; rewrite !ffunE /join.
      case A: (a l == vundef)=> //.
      case B: (b l == vundef)=> //.
      rewrite A.
      case C: (c l == vundef)=> //.
      case C: (c l == vundef)=> //.
      rewrite B. 
      case V: (vundef == vundef)=> //.
      by rewrite (eqP C).
      case V: (vundef == vundef)=> //.
      elimtype False.
      move: H1; rewrite /dom; move/forallP; move/(_ l).
        by rewrite A B; move/orP; case; discriminate.
    Qed.    

    Lemma opC a b : dom a b -> op a b = op b a.
    Proof.
      move=> H; rewrite /op -ffunP=> l; rewrite !ffunE /join.
      case A: (a l == vundef)=> //.
      case B: (b l == vundef)=> //.
        by move: (eqP A); move: (eqP B)=> -> ->.
    Qed.        

    Lemma domC a b : dom a b = dom b a.
    Proof.
      rewrite /dom; apply: eq_forallb=> l.
      case: (a l == vundef)=> /=; first by rewrite orbC.
        by case: (b l == vundef).
    Qed.
      
    Lemma edom a : dom e a.
    Proof.
      rewrite /dom /e; apply/forallP=> l; rewrite ffunE.
        by apply/orP; left; apply/eqP.
    Qed.

    Lemma opeUL a : op e a = a.
    Proof. by rewrite /op /e -ffunP=> l; rewrite ffunE /join ffunE eq_refl. Qed.

    Definition mixin :=
      @PCM.Mixin heap op dom e opA opC domC edom opeUL.
    Canonical t := Eval hnf in PcmType heap mixin.
  End heapPCM.
End HeapPCM.
  
Module GraphPCM.
  Section graphPCM.
    Variable T : finType. (*the type of vertices*)
    Variables src snk : T. (*the source and sink*)
    Variables edges : rel T.
    Definition raw_path := {n : 'I_#|T| & n.-tuple T}.
    Definition ok_path : pred raw_path :=
      [pred p : raw_path
      | [&& path edges src (projT2 p) & last src (projT2 p) == snk]].
    (*if path is empty, src = snk*)
    Definition path := {p : raw_path | ok_path p}.
    Definition pathset := {set path}.
    
    Definition op (a b : pathset) : pathset := a :|: b.

    Definition dom (a b : pathset) := true.
    
    Definition e : pathset := set0.
                    
    Lemma opA a b c :
      dom a b -> dom (op a b) c -> dom b c -> dom a (op b c) ->
      op (op a b) c = op a (op b c).
    Proof. by move=> H1 H2 H3 H4; rewrite /op setUA. Qed.

    Lemma opC a b : dom a b -> op a b = op b a.
    Proof. by rewrite /op setUC. Qed.

    Lemma domC a b : dom a b = dom b a.
    Proof. by []. Qed.
      
    Lemma edom a : dom e a.
    Proof. by []. Qed.

    Lemma opeUL a : op e a = a.
    Proof. by rewrite /op set0U. Qed.

    Definition mixin :=
      @PCM.Mixin pathset op dom e opA opC domC edom opeUL.
    Canonical t := Eval hnf in PcmType pathset mixin.
  End graphPCM.
End GraphPCM.
