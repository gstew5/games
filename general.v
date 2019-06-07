Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Def Num.Theory.

(** General lemmas *)

Lemma eqr_add2l:
  forall (T0: ringType) (a b c: T0),
  b = c -> (a + b)%R = (a + c)%R.
Proof.
    by move=> T0 a b c Hbc; rewrite Hbc.
Qed.

Lemma iter_add_const:
  forall (T: ringType) (x: T) (n : nat),
  iter n (+%R x) 0%R = (x *+ n)%R.
Proof.
move=>T0 x. elim => [//|n IHn] => //=.
rewrite mulrSr (addrC _ x) .
  by  apply (eqr_add2l T0 x); rewrite IHn.
Qed.

Lemma iter_mul_0:
  forall (T: ringType) (n : nat),
  n > 0 -> iter n ( *%R (0:T)%R) 1%R = (0:T)%R.
Proof.
move=>T0 [] //=.
by elim => [| n IHn] => Hgt //=; rewrite mul0r.
Qed.

Lemma iter_mul_1:
  forall (T: ringType)  (n : nat),
  iter n ( *%R (1:T)%R) 1%R = (1:T)%R.
Proof.
move=>T0 . elim => [//|n IHn] => //=.
  by rewrite IHn  mul1r.
Qed.

Lemma sum_eq0:
  forall (T0: ringType) (X: finType),
  (\sum_(i:X) 0)%R = (0:T0)%R.
Proof.
move=> T0 N.
  by rewrite big_const iter_add_const mul0rn.
Qed.

Lemma sum_pred_eq0:
  forall (T0: ringType) (X: finType) (P : pred X),
  (\sum_(i:X | P i) 0)%R = (0:T0)%R.
Proof.
move=> T0 X P.
  by rewrite big_const iter_add_const mul0rn.
Qed.

Lemma prod_eq1:
  forall (T0: ringType) (n: nat),
  (\prod_(i < n) 1)%R = (1:T0)%R.
Proof.
move=>T0 n.
rewrite big_const iter_mul_1 => //=.
Qed.

Lemma forallD1:
  forall (T : finType) (x:T) (P: pred T),
  ((P x && [forall (y:T| x != y), P y == true]) -> [forall y:T, P y]).
Proof.
move=>T x P.
case (boolP (P x)) => //=.
move=> Hpx Hforall.
apply/forallP => y.
case (boolP (x == y)) => //=.
+ by move/eqP => <-.
+ by move=> Hxy; move/forallP/(_ y)/implyP/(_ Hxy)/eqP: Hforall.
Qed.
