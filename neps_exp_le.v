Require Import Reals Fourier Omega.

(*** Basic idea:

To prove that (1-yx) >= (1-y)^x, 
use the following result:

Lemma derive_increasing_interv :
forall (a b:R) (f:R -> R) (pr:derivable f),
    a < b ->
    (forall t:R, a < t < b -> 0 < derive_pt f t (pr t)) ->
    forall x y:R, a <= x <= b -> a <= y <= b -> x < y -> f x < f y.

Here, f is GF(x).  a=0, b=1. 

Now, The derivative of GF(x) y = -x - -x/(1-y)^{1-x} > 0 for
all y between 0 and 1 because (1-y)^{1-x} < 1 in this range. 

***)

Definition g (x:R):=x.
Lemma derivable_g: forall x:R, derivable_pt g x.
Proof.
intros.
unfold g.
apply derivable_pt_id.
Defined.

Lemma derivable_g_all: forall a b:R, forall c:R, a < c < b -> derivable_pt g c.
Proof.
intros.
apply derivable_g.
Defined.

Lemma derive_pt_g: forall (x:R),
derive_pt g x (derivable_g x) = 1.
Proof.
intros.
unfold g.
apply derive_pt_id.
Defined.

(* 

This file attempts to establish that 

(1-y)^x <= (1-y*x) for all x in [0,1] and y in [0, 1/2].
Notice that 

a.) When y=1, this function becomes 0^x <= (1-x).
Now, in COQ, 0^x = e^x*ln(0).   Since ln0 is undefined, I believe
0^x is undefined as well.

*)

Definition GF x y:R := ((1-y*x) - (Rpower (1-y) x)).

(* Boundary cases *)

Theorem GF_y_0: forall x:R, 0=GF x 0.
Proof.
intros.
unfold GF.
unfold Rpower.
assert (1-0 = 1).
field.
rewrite H.
rewrite ln_1.
assert (x*0=0).
field.
rewrite H0.
rewrite exp_0.
field.
Qed.
Theorem GF_x_0: forall y:R, 0<=y<=(1/2)-> 0=GF 0 y.
Proof.
intros.
unfold GF.
assert (0<1-y).
destruct H.
fourier.
rewrite Rpower_O.
field.
auto.
Qed.

Theorem GF_x_1: forall y:R, 0<=y<=(1/2)-> 0=GF 1 y.
Proof.
intros.
unfold GF.
assert (0<1-y).
destruct H.
fourier.
rewrite Rpower_1.
field.
auto.
Qed.

(** If GF is at least 0, then his result holds.  **)

Lemma a1: forall x y:R, 0<=(GF x y)-> (Rpower (1-y) x) <= 1-y*x.
Proof.
intros.
unfold GF in H.
destruct H.
left.
apply Rminus_gt;auto.
right.
symmetry.
apply Rminus_diag_uniq.
auto.
Qed.

Lemma a2:forall x y:R, 
0<x<1 -> 
0<y<1 -> 
0< (Rpower (1-y) (1-x)) < 1.
Proof.
intros.
split.
unfold Rpower.
apply exp_pos.
unfold Rpower.
assert (1-y < 1).
destruct H0.
destruct H.
fourier.
assert ((1-x) < 1).
destruct H0.
destruct H.
fourier.
assert ((ln (1-y)) < 0).
assert (ln 1 =0).
apply ln_1.
rewrite <-H3.
apply ln_increasing.
destruct H0.
fourier.
exact H1.
assert ((1-x)*(ln (1-y)) < 0).
assert (1-x >0).
destruct H.
fourier.
assert ((1-x)*0 = 0).
field.
rewrite <-H5.
apply Rmult_lt_compat_l.
auto.
auto.
assert (exp 0 = 1).
apply exp_0.
rewrite <-H5 at 3.
apply exp_increasing.
auto.
Qed.

Theorem derivable_pt_ln: forall x:R, 0<x -> derivable_pt ln x.
Proof.
intros.
unfold derivable_pt.
unfold derivable_pt_abs.
exists (/x).
apply derivable_pt_lim_ln.
auto.
Defined. 
Lemma derive_pt_ln :
  forall x:R, forall (h1: 0<x), derive_pt ln x (derivable_pt_ln x h1) =  /x.
Proof.
  intros.
 apply derive_pt_eq_0.
  apply derivable_pt_lim_ln.
  auto.
Qed.

Theorem dir1: forall x y:R, 0<x<1 -> 0<y<=(1/2)-> (derivable_pt (GF x) y).
Proof.
intros.
assert (0<1-y).
destruct H0.
fourier.
unfold GF.
apply derivable_pt_minus.
apply derivable_pt_minus.
apply derivable_pt_const.
apply derivable_pt_mult.
apply derivable_pt_id.
apply derivable_pt_const.
(* First half done *)
unfold Rpower.
set (f:=fun y=> x*ln(1-y)).
assert (derivable_pt (comp exp f) y).
apply derivable_pt_comp.
unfold f.
apply derivable_pt_mult.
apply derivable_pt_const.
apply derivable_pt_comp.
apply derivable_pt_minus.
apply derivable_pt_const.
apply derivable_pt_id.
apply derivable_pt_ln.
exact H1.
apply derivable_pt_exp.
unfold comp,f in H2.
auto.
Defined.

Theorem dir1_1: forall x y:R, 0<=x -> 0<=y<=(1/2)-> (derivable_pt (GF x) y).
Proof.
intros.
assert (0<1-y).
destruct H0.
fourier.
unfold GF.
apply derivable_pt_minus.
apply derivable_pt_minus.
apply derivable_pt_const.
apply derivable_pt_mult.
apply derivable_pt_id.
apply derivable_pt_const.
(* First half done *)
unfold Rpower.
set (f:=fun y=> x*ln(1-y)).
assert (derivable_pt (comp exp f) y).
apply derivable_pt_comp.
unfold f.
apply derivable_pt_mult.
apply derivable_pt_const.
apply derivable_pt_comp.
apply derivable_pt_minus.
apply derivable_pt_const.
apply derivable_pt_id.
apply derivable_pt_ln.
exact H1.
apply derivable_pt_exp.
unfold comp,f in H2.
auto.
Defined.

Theorem dir_c_1:forall x y:R, 0<=x -> 0 <= y <= 1/2 -> continuity_pt (GF x) y.
Proof.
intros.
apply derivable_continuous_pt.
apply dir1_1; auto.
Qed.

Theorem dir_c_g: forall y:R, continuity_pt g y.
Proof.
intros.
apply derivable_continuous_pt.
apply derivable_g.
Qed.

(* Interesting lemma ---
   for every x y:R, and for every proof that 
   0<=x and 
   0<=y<=(1/2)),
   the derivative of GF x y (wrt y) is >0.
*)

Theorem ab2: forall x y:R, 0<x<1 -> 0<y<=1/2 -> 
x < x*(/(Rpower (1-y) (1-x))).
Proof.
intros.
assert (0<y<1).
destruct H0.
split;auto.
fourier.
assert ((Rpower (1-y) (1-x)) < 1).
apply a2.
auto.
auto.
assert (/1 = 1).
field.
assert (1 < (/(Rpower (1-y) (1-x)))).
rewrite <-H3 at 1.
apply Rinv_lt_contravar.
assert ((Rpower (1-y) (1-x))*1 = (Rpower (1-y) (1-x))).
field.
rewrite H4.
apply a2.
auto.
auto.
exact H2.
assert (x*1 = x).
field.
rewrite <-H5 at 1.
apply Rmult_lt_compat_l.
destruct H.
auto.
exact H4.
Qed.

Lemma Rminus_gt_comp: forall a b:R, a<b -> 0<b-a.
Proof.
intros.
fourier.
Qed.

Theorem ab: forall x y:R, forall (h1:0<x<1) (h2:0<y<=(1/2)), 
  0<(derive_pt (GF x) y (dir1 x y h1 h2)).
Proof.
intros.
unfold GF.
unfold Rpower.
set (f:=fun y0 => (exp (x*(ln (1-y0))))).
set (f1:=fun y1 => 1-y1*x).
unfold dir1.
rewrite (derive_pt_minus f1 f).
unfold f1.
rewrite (derive_pt_minus (fun x0=>1) (fun y0=>y0*x)).
rewrite (derive_pt_const 1).
rewrite (derive_pt_mult (fun y0=>y0) (fun y1=>x)).
rewrite derive_pt_id.
rewrite (derive_pt_const x).
unfold f.
rewrite (derive_pt_comp  (fun y0=>x*(ln (1-y0))) exp).
set (z:=x*(ln 1-y)).
rewrite (derive_pt_exp (x * ln (1 - y))).
rewrite (derive_pt_mult (fun x0=>x) (fun y0=>ln (1-y0))).
rewrite (derive_pt_const x).
rewrite (derive_pt_comp (fun y0=>1-y0) ln).
rewrite derive_pt_ln.
rewrite (derive_pt_minus (fun x0=>1) (fun y0=>y0)).
rewrite (derive_pt_const 1).
rewrite derive_pt_id.
simpl.
assert ((0 - (1*x +y*0)) = -x).
ring.
rewrite H.
assert (exp (x * ln (1 - y)) = (Rpower (1-y) x)).
unfold Rpower.
reflexivity.
rewrite H0.
assert (0*ln(1-y) = 0).
ring.
rewrite H1.
assert ((/(1 - y) * (0 - 1)) = -(/(1-y))).
field.
destruct h2.
assert (0<1-y).
fourier.
apply Rgt_not_eq.
exact H4.
rewrite H2.
assert (((Rpower (1 - y) x) * (0 + x * - / (1 - y))) = -x*(/(1-y))*(Rpower (1-y) x)).
field.
assert (0<1-y).
destruct h2.
fourier.
apply Rgt_not_eq.
exact H3.
rewrite H3.
assert ((1-y) = (Rpower (1-y) 1)).
rewrite Rpower_1.
reflexivity.
destruct h2.
fourier.
rewrite H4 at 1.
assert ((/(Rpower (1-y) 1)) = (Rpower (1-y) (- 1))).
rewrite Rpower_Ropp.
reflexivity.
rewrite H5.
assert ((-x*Rpower (1-y) (- 1))*(Rpower (1-y) x)=-x*(Rpower (1-y) (-1 + x))).
rewrite Rmult_assoc at 1.
rewrite Rpower_plus.
reflexivity.
rewrite H6.
assert ((Rpower (1-y) (-1 + x)) = (/(Rpower (1-y) (1-x)))).
assert (-(1-x) = (-1 + x)).
ring.
rewrite <-H7.
rewrite Rpower_Ropp.
reflexivity.
rewrite H7.
assert ((-x -- x*(/(Rpower (1-y) (1-x)))) = x*(/(Rpower (1-y) (1-x))) - x).
ring.
rewrite H8.
assert (x< x*/(Rpower (1-y) (1-x))).
apply ab2.
exact h1.
exact h2.
apply Rminus_gt_comp.
exact H9.
Qed.

Theorem simpl1: forall a b c:R, a<b<c -> a<b<=c.
Proof.
intros.
split.
destruct H;auto.
left.
destruct H.
auto.
Defined.

Theorem simpl2: forall a b c d:R, a<b<c -> c <=d -> a<b<=d.
Proof.
intros.
destruct H.
split.
auto.
left.
apply (Rlt_le_trans b c d);auto.
Qed.

Theorem simpl3: forall a b c d:R, a<b<c -> c<=d -> a<=b<=d.
Proof.
intros.
destruct H.
split.
left;auto.
left.
apply (Rlt_le_trans b c d);auto.
Defined.

Theorem simpl4: forall a b c:R, a<b<c -> a<=b.
Proof.
intros.
destruct H.
left;auto.
Defined.

Theorem test1:
  forall x y:R,
  forall (pr: 0<x<1) (pr:0<y<=1/2),
  forall c:R, 0<c<y->derivable_pt (GF x) c.
Proof.
intros.
apply dir1.
exact pr.
destruct pr0.
destruct H.
split.
auto.
left.
apply (Rlt_le_trans c y (1/2));auto.
Defined.

Theorem Rmult_lt_pos: forall a b:R, 0<a -> 0<b -> 0<a*b.
Proof.
intros.
assert (0*b = 0).
field.
rewrite <-H1.
apply Rmult_lt_compat_r;auto.
Qed.

Theorem deriv_int: forall x y:R, 0<x<1 -> 0<y<=(1/2) ->
  (GF x) y - (GF x) 0 > 0.
Proof.
intros.
set (f:= fun y=> GF x y).
set (H2:=(test1 x y H H0)).
destruct H0.
assert (exists c:R, (exists P: 0<c <y,
(g y - g 0) * derive_pt f c (H2 c P) =
        (f y - f 0) * derive_pt g c (derivable_g_all 0 y c P))).
apply (MVT f g 0 y (H2) (derivable_g_all 0 y)).
exact r.
intros.
apply dir_c_1.
apply (simpl4 0 x 1).
exact H.
split.
destruct H0;auto.
destruct H0.
apply (Rle_trans c y (1/2));auto.
intros.
apply dir_c_g.
destruct H0.
destruct H0.
assert (derive_pt g x0 (derivable_g_all 0 y x0 x1) = 1).
unfold derivable_g_all.
apply derive_pt_g.
rewrite  H1 in H0.
unfold g in H0.
assert (f 0 = 0).
simpl.
unfold f.
unfold GF.
unfold Rpower.
assert (1-0 = 1).
field.
rewrite H3.
rewrite ln_1.
assert (x*0 = 0).
field.
rewrite H4.
rewrite exp_0.
field.
rewrite H3 in H0.
unfold H2 in H0.
unfold test1 in H0.
assert (0<derive_pt f x0
       (dir1 x x0 H
          match x1 with
          | conj H H2 =>
              conj H
                (or_introl
                   (Rlt_le_trans x0 y 
                      (1 / 2) H2 r0))
          end)).
apply ab.
assert (((f y) - 0 )*1 = f y).
field.
assert (f y - f 0 = f y).
rewrite H3.
field.
rewrite H6.
assert ((y-0)=y).
field.
rewrite H7 in H0.
rewrite H5 in H0.
assert (0<y *
     derive_pt f x0
       (dir1 x x0 H
          match x1 with
          | conj H H2 =>
              conj H
                (or_introl
                   (Rlt_le_trans x0 y 
                      (1 / 2) H2 r0))
          end)).
apply Rmult_lt_pos;auto.
rewrite <-H0.
auto.
Qed.

Theorem dir2: forall x y:R, 0<x<1 -> 0<y<=1/2 -> 0< (GF(x) y).
Proof.
intros.
set (f:= fun y0 => GF x y0).
assert (f 0 = 0).
simpl.
unfold f.
unfold GF.
unfold Rpower.
assert (1-0 = 1).
field.
rewrite H1.
rewrite ln_1.
assert (x*0 = 0).
field.
rewrite H2.
rewrite exp_0.
field.
rewrite <-H1.
unfold f.
assert (0<GF x y - GF x 0).
apply deriv_int.
exact H.
exact H0.
apply (Rplus_lt_reg_r (-GF x 0) (GF x 0) (GF x y)).
assert ((GF x 0) + - (GF x 0)=0).
field.
rewrite H3.
exact H2.
Qed.

Theorem neps_exp_le:
  forall x y:R, 0<=x<=1-> 0<=y<=1/2 -> 
  (Rpower (1-y) x) <= 1-y*x.
Proof.
intros.
apply (a1 x y).
destruct H.
(* apply dir2 for all of the non boundary cases *)
destruct H0.
destruct H.
destruct H1.
destruct H0.
left.
apply dir2.
auto.
auto.
right.
rewrite <-H0.
apply (GF_y_0 x).
rewrite H1.
right.
apply (GF_x_1 y).
auto.
right.
rewrite <-H.
apply (GF_x_0 y).
auto.
Qed. 
