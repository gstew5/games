Set Implicit Arguments.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import games.

Local Open Scope ring_scope.

Section stepDefs.
  Context {T : Type}.
  Variable step : T -> T -> Prop.
  Variable halted : T -> Prop.
  Hypothesis haltedP : forall t t', halted t -> step t t' -> False.
  
  Fixpoint stepN (n : nat) : T -> T -> Prop :=
    [fun t t' =>
       if n is S n' then
         exists t'', [/\ step t t'' & stepN n' t'' t']
       else t = t'].

  Lemma stepN_plus n m t'' {t t'} :
    stepN n t t'' ->
    stepN m t'' t' ->
    stepN (n + m)%coq_nat t t'.
  Proof.
    elim: n t t'' t'=> //=; first by move=> t t'' t' <-.
    move=> n IH t t'' t' []tx []H1 H2 H3.  
    exists tx; split=> //; apply: (IH _ _ _ H2 H3).
  Qed.    

  Inductive step_star : T -> T -> Prop :=
  | step_refl t : step_star t t
  | step_trans t'' t t' :
      step t t'' ->
      step_star t'' t' ->
      step_star t t'.
  Arguments step_trans t'' [t t'] _ _.

  Lemma step_trans2 t t'' t' :
    step_star t t'' ->
    step_star t'' t' ->
    step_star t t'.
  Proof.
    move=> H; move: t'.
    elim: H=> //.
    move {t t''}. 
    move=> t'' t t' H H2 IH tx H3.
    apply: (step_trans _ H).
    by apply: IH.
  Qed.       
  
  Lemma stepN_step_star t t' :
    (exists n, stepN n t t') <-> step_star t t'.
  Proof.
    split.
    { move=> []n H; move: t t' H; elim: n.
      { move=> t t'/= <-; constructor.
      }
      move=> n IH t t' /= []t'' []H1 H2.
      apply: (step_trans t'')=> //.
      by apply: (IH _ _ H2).
    }
    elim.
    { by move=> t''; exists O.
    }
    move=> t'' ta tb H H1 []n H2.
    by exists (S n), t''; split.
  Qed.

  Definition safe t :=
    forall t'', step_star t t'' ->
    [\/ exists t', step t'' t'| halted t'']. 

  Lemma safe_step t t' :
    safe t ->
    step t t' ->
    safe t'.
  Proof.
    move=> H H2 t'' H3.
    case: (H t'').
    { apply: (step_trans _ H2 H3).
    }
    by case=> x H4; left; exists x.
    by move=> ?; right.
  Qed.

  Lemma safe_step_star t t' :
    safe t ->
    step_star t t' ->
    safe t'.
  Proof.
    move=> H H2.
    elim: H2 H=> //.
    move=> t'' tx ty H H2 IH H3.
    apply: IH.
    apply: (safe_step H3 H).
  Qed.    
    
  (* Every path halts *)
  
  Definition everywhere_halts (t : T) :=
    forall t'', step_star t t'' ->
    exists t', [/\ step_star t'' t' & halted t'].

  Lemma everywhere_halts_step t t' :
    everywhere_halts t ->
    step t t' ->
    everywhere_halts t'.
  Proof.
    rewrite /everywhere_halts => H H2 t'' H3.
    case: (H t'')=> /=; first by apply: (step_trans _ H2 H3).
    move=> tx []H4 H5.
    exists tx; split=> //.
  Qed.                            

  Lemma everywhere_halts_step_star t t' :
    everywhere_halts t ->
    step_star t t' ->
    everywhere_halts t'.
  Proof.
    move=> H H2; move: H; elim: H2=> //.
    move=> t'' tx ty H H2 IH H3.
    apply: IH.
    apply: (everywhere_halts_step H3 H).
  Qed.    

  (* Some path halts *)
  
  Definition halts (t : T) :=
    exists t', [/\ step_star t t' & halted t'].

  Lemma halts_step t t' :
    halts t' -> 
    step t t' ->
    halts t.
  Proof.
    case=> x []H H2 H3; exists x; split=> //.
    by apply: (step_trans _ H3).
  Qed.    
  
  Lemma everywhere_halts_halts t : everywhere_halts t -> halts t.
  Proof.
    move/(_ t); case; first by apply: step_refl.
    move=> t' []H H2; exists t'; split=> //.
  Qed.
End stepDefs.

Section history.
  Context `{gameClass : game}.
  Notation sT := (state N T).
  Context {step : sT -> sT -> Prop}.

  Let hstate := (simpl_pred sT*simpl_pred sT*sT)%type.
  
  (** [P] is a user-supplied induction principle, used to prove 
      the well-foundedness of the step relation for game [sT]. *)
  Variable P : hstate -> Prop.
  
  Inductive hstep : hstate -> hstate -> Prop :=
  | hstep_step (s u : simpl_pred sT) t t' :
      let: s' := predU1 t' s in
      let: u' := predD1 u t' in
      u t' ->
      step t t' ->
      hstep (s,u,t) (s',u',t').
  
  Definition inv (sut : simpl_pred sT*simpl_pred sT*sT) : Prop :=
    let: (s,u,t) := sut
    in [/\ predU s u =1 fun x => x \in (enum sT)
         , predI s u =1 fun _ => false
         & s t]. 

  Definition init (t : sT) := (pred1 t, predD1 predT t, t).
  
  Lemma inv_init t : inv (init t).
  Proof.
    split=> //=.
    { move=> x /=; case: (x == t)=> //=.
      rewrite (mem_enum sT x) //.  
      rewrite (mem_enum sT x) //.
    }
    move=> x /=; case: (x == t)=> //.
  Qed.                                    

  Hypothesis init_P : forall t, P (init t).
  Hypothesis step_P :
    forall s u t t',
      inv (s,u,t) -> P (s,u,t) -> step t t' -> 
      [/\ u t' & P (predU1 t' s, predD1 u t', t')].
      
  Lemma hstep_inv sut sut' :
    inv sut -> P sut -> 
    hstep sut sut' -> 
    [/\ inv sut' & P sut'].
  Proof.
    case: sut=> [][]s u t; case: sut'=> [][]s' u' t' H1 Hx H2; move: H1.
    inversion H2; subst.
    split.
    { case: H1=> H4 H5; split.
      { move=> x /=.
        move: (H4 x)=> /= <-.
        case H9: (s x)=> //=.
        by case H10: (x == t')=> //=.
        move: (H4 x).
        rewrite (mem_enum sT x)=> /=.
        rewrite H9=> /= -> //.
        by case: (x == t')=> //.
      }
      move=> x /=.
      move: (H5 x)=> /=.
      case H9: (s x)=> //=.
      move=> -> //.
      by case: (x == t').
      move=> _.
      by case: (x == t').
      by simpl; rewrite eq_refl.
    }
    inversion H2; subst. move {H7 H9}.
    by case: (step_P H1 Hx H11).
  Qed.
  
  Lemma step_hstep su t t' :
    inv (su,t) -> P (su,t) -> step t t' ->
    exists su',
      [/\ hstep (su,t) (su',t') & P (su',t')].
  Proof.
    case: su=> s u H0 H2.
    exists (predU1 t' s, predD1 u t').
    case: (step_P H0 H2 H1)=> ??.
    split=> //.                               
  Qed.

  Lemma step_star_hstep_star su t t' :
    inv (su,t) -> P (su,t) -> step_star step t t' ->
    exists su',
      [/\ step_star hstep (su,t) (su',t') & P (su',t')].
  Proof.
    move=> H0 Hx H2.
    elim: H2 su H0 Hx.
    { move=> tx su H0 Hx.
      exists su.
      split=> //.
      apply: step_refl.
    }
    move {t t'}.
    move=> t'' t t' H0 H2 IH su H3 Hx.
    case: (step_hstep H3 Hx H0)=> []su'' []H4 H5.
    have H6: inv (su'',t'').
    { by case: (hstep_inv H3 Hx H4).
    }
    case: (IH su'' H6 H5)=> su' []H7 H8.
    exists su'.
    split=> //.
    apply: (step_trans _ H4 H7).
  Qed.    

  Lemma hstep_star_inv sut sut' :
    inv sut -> P sut -> 
    step_star hstep sut sut' -> 
    [/\ inv sut' & P sut'].
  Proof.
    move=> H0 Hx H2; elim: H2 H0 Hx=> //t'' t t' H0 H2 IH H3 Hx.
    case: (hstep_inv H3 Hx H0).
    apply: IH.
  Qed.    
  
  Definition hist2nat (sut : hstate) : nat :=
    let: (s,u,t) := sut in #|u|.

  Lemma hstep_ord sut sut' : 
    hstep sut sut' -> 
    (hist2nat sut' < hist2nat sut)%coq_nat.
  Proof.
    case: sut=> [][]s u t; case: sut'=> [][]s' u' t' H0.
    case: H0; move {s u t s' u' t'}=> s u t t' H0 H2.
    by rewrite /hist2nat /= (cardD1 t' u) /in_mem /= H0.
  Qed.

  Variable halted : sT -> Prop.
  Hypothesis halted_doesnt_step : forall t t', halted t -> step t t' -> False.
  
  Definition hstep_halted (sut : hstate) :=
    [\/ halted sut.2 | hist2nat sut = O].
  
  Lemma hstep_star_step_star s u t s' u' t' :
    step_star hstep (s,u,t) (s',u',t') -> 
    step_star step t t'.
  Proof.
    have Hx: (s,u,t).2 = t by [].
    have Hy: (s',u',t').2 = t' by [].
    move: Hx Hy.
    move: (s,u,t)=> sut.
    move: (s',u',t')=> sut'.
    move=> <- <-.
    move {s u t s' u' t'}.
    elim.
    { move=> t; apply: step_refl.
    }
    move=> t'' t t' H0 H2 H3; inversion H0; subst; simpl in *.
    by apply: (step_trans _ H4).
  Qed.      
  
  Lemma safe_step_hstep s u t :
    inv (s,u,t) ->
    P (s,u,t) -> 
    safe step halted t ->
    safe hstep hstep_halted (s,u,t).
  Proof.
    move=> H0 Hx H1 [][]s' u' t' H2.
    case: (H1 t').
    { by apply: (hstep_star_step_star H2).
    }
    { case=> tx H3.
      have H4: inv (s',u',t').
      { by case: (hstep_star_inv H0 Hx H2).
      }
      have Hy: P (s',u',t').
      { by case: (hstep_star_inv H0 Hx H2).
      }
      case: (step_hstep H4 Hy H3)=> sux []??.
      by left; exists (sux,tx).
    }
    by move=> H3; right; left.
  Qed.    
    
  Lemma hstep_halts_or_stuck sut :
    safe hstep hstep_halted sut -> 
    halts hstep hstep_halted sut.
  Proof.
    remember (hist2nat sut).
    elim: n sut Heqn.
    { rewrite /halts /hstep_halted => sut H0.
      exists sut; split.
      { apply: step_refl.
      }
      by rewrite H0; right.
    }
    move=> n IH sut H0 H2.
    case: (H2 sut); first by apply step_refl.
    { case=> sut' H3.
      have H4: halts hstep hstep_halted sut'.
      { apply: IH.
        { inversion H3; subst.
          simpl in H0|-*.
          rewrite (cardD1 t') /in_mem /= H1 /= in H0.
          by case: H0=> <-.
        }
        apply: (safe_step H2 H3).
      }
      apply: (halts_step sut H4 H3).
    }
    move=> H3.
    exists sut; split=> //.
    apply: step_refl.                          
  Qed.

  Lemma hstep_everywhere_halts_or_stuck sut :
    safe hstep hstep_halted sut ->
    everywhere_halts hstep hstep_halted sut.
  Proof.
    move=> H0 sut' H2.
    have H3: safe hstep hstep_halted sut'.
    { apply: (safe_step_star H0 H2).
    }
    case: (hstep_halts_or_stuck H3)=> sut'' []H4 H5.
    exists sut''; split=> //.
  Qed.

  Lemma halted_doesnt_hstep sut sut' :
    hstep_halted sut ->
    hstep sut sut' ->
    False.
  Proof.
    case=> H0.
    { inversion 1; subst.
      apply: (halted_doesnt_step H0 H3).
    }
    inversion 1; subst.
    rewrite /= (cardD1 t') /in_mem /= H2 /= in H0=> //.
  Qed.                                                     
  
  Lemma everywhere_halts_hstep_step sut :
    safe step halted sut.2 -> 
    inv sut -> P sut -> 
    everywhere_halts hstep hstep_halted sut ->
    everywhere_halts step halted sut.2.
  Proof.
    case: sut=> [][]s u t.
    move=> Hx H0 Hy /= H1 t' H2.
    rewrite /fst in H0.
    case: (step_star_hstep_star H0 Hy H2)=> [][]s' u' []H3 Hz.
    case: (H1 _ H3)=> x []H4 H5.
    case: x H4 H5=> [][]s'' u'' t'' H4 H5.
    move: (hstep_star_step_star H4)=> H6.
    exists t''; split=> //.
    rewrite /= in Hx.                          
    have H7: safe step halted t''.
    { apply: (safe_step_star (t:=t))=> //.
      apply: (step_trans2 H2 H6).
    }
    case: (H7 t'')=> //; first by apply: step_refl.
    case=> tx H8.
    have H9: [/\ inv (s'',u'',t'') & P (s'',u'',t'')].
    { have H10: step_star hstep (s,u,t) (s'',u'',t'').
      { apply: (step_trans2 H3 H4).
      }
      apply: (hstep_star_inv H0 Hy H10).      
    }
    case: H9=> H9 H10.
    case: (step_hstep H9 H10 H8)=> [][]sx ux.
    inversion 1; subst.
    case: p=> Hu ?.
    elimtype False.
    apply: (halted_doesnt_hstep H5 Hu).
  Qed.    
  
  Lemma step_everywhere_halts_or_stuck t :
    safe step halted t ->
    everywhere_halts step halted t.
  Proof.
    set init := (pred1 t, predD1 predT t, t).
    have H2: inv init by apply: inv_init.
    move=> H1; have Hx: t = init.2 by [].
    rewrite Hx.
    apply: (everywhere_halts_hstep_step)=> //.
    apply: init_P.
    apply: hstep_everywhere_halts_or_stuck.
    apply: safe_step_hstep=> //.
    apply: init_P.                               
  Qed.                               
End history.
