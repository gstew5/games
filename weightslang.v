Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import dist weights.

(** An extremely simple probabilistic programming language, 
    used to implement multiplicative weights update (weights.v) *)

Inductive val : Type :=
| QVal : Q -> val.

Inductive binop : Type := BPlus | BMult.

Section com.
  Variable A : Type. (* The game type *)

  Inductive expr : Type :=
  | EVal : val -> expr
  | EOpp : expr -> expr
  | EWeight : A -> expr 
  | ECost : A -> expr
  | EEps : expr            
  | EBinop : binop -> expr -> expr -> expr.

  Inductive com : Type :=
  | CUpdate : (A -> expr) -> com
  | CRecv : com
  | CSend : com
  | CSeq : com -> com -> com
  | CRepeat : com -> com.
End com.

Arguments EVal [A] _.
Arguments EEps [A].

Arguments CRecv [A].
Arguments CSend [A].
Arguments CRepeat [A] _.

Definition mult_weights (A : Type) : com A :=
  CRepeat
    (CSeq
       CRecv
       (CSeq (CUpdate (fun a : A =>
                         (EBinop BMult
                              (EWeight a)
                              (EBinop BPlus
                                      (EVal (QVal 1))
                                      (EBinop BMult EEps (ECost a))))))
             CSend)).

Section semantics.
  Local Open Scope ring_scope.
  Variable A : finType.

  Record state : Type :=
    mkState
      { SCosts :  {ffun A -> Q} (* the current cost vector *)
      ; SPrevCosts : seq {ffun A -> Q} (* reverse-chronological list of cost vectors seen so far *)
      ; SWeights : {ffun A -> Q} (* current weights *)
      ; SEpsilon : Q }. (* epsilon -- a parameter *)

  Fixpoint eval (e : expr A) (s : state) : val :=
    match e with
    | EVal v => v
    | EOpp e' => let: QVal v := eval e' s in QVal (- v)
    | EWeight a => QVal (SWeights s a)
    | ECost a => QVal (SCosts s a)
    | EEps => QVal (SEpsilon s)
    | EBinop b e1 e2 =>
      let: QVal v1 := eval e1 s in
      let: QVal v2 := eval e2 s in
      QVal (v1 + v2)
    end.
  
  Inductive step : com A -> state -> state -> Prop :=
  | SUpdate :
      forall f s s',
        s' = mkState
               (SCosts s)
               (SPrevCosts s)
               (finfun (fun a => let: QVal v := eval (f a) s in v))
               (SEpsilon s) -> 
        step (CUpdate f) s s'
             
  | SRecv :
      forall c s s',
        s' = mkState
               c
               (SCosts s :: SPrevCosts s)
               (SWeights s)
               (SEpsilon s) ->
        step CRecv s s'

  | SSend :
      forall s,
        step CSend s s (*Question: is "send" a semantic no-op?*)

  | SSeq :
      forall c1 c2 s1 s2 s3,
        step c1 s1 s2 ->
        step c2 s2 s3 ->
        step (CSeq c1 c2) s1 s3

  | SRepeat :
      forall c s s',
        step (CSeq c (CRepeat c)) s s' ->
        step (CRepeat c) s s'.
End semantics.
