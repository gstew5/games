Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import BinNat Nnat.

Require Import dist.

Section sample.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Variable t0 : T. (* assume the distribution is inhabited *)
  
  Definition sample : T :=
    bind (uniformDist T)
         (fun t => 
    
    let: u := uniformDist T in
    bind u (fun x =>
    inverse_cdf d (x / #|T|).
                
  