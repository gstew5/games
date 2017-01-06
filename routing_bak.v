Set Implicit Arguments.
Unset Strict Implicit.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import games potential.

Section AtomicRoutingGame.
  Variable T : finType. (** The type of nodes *)
  Variable num_players : nat. (** The number of players *)
  Variable rty : realFieldType.

  (** We represent graphs by their adjacency matrices *)
  Variable g : 'M[bool]_(#|T|, #|T|).
  
  (** Edge costs are modeled by a function mapping 
        - node i  : #|T|    The source node for this edge
        - node j  : #|T|    The target node for this edge
        - traffic : nat     The amount of traffic over this edge
      to a real number type [rty]. *)
  Variable ecosts : forall x y : 'I_#|T|, nat -> rty.

  (** Players are pairs of source-sink vertices. *)
  Record player : Type :=
    mkPlayer {
        source : 'I_#|T|;
        sink : 'I_#|T|
      }.
  Variable players : 'I_num_players -> player.

  Definition path := ('I_#|T| ^ #|T|)%type.

  (** A path [p] is a source-sink path from [x] to [y] if either
      - p x = y AND x->y is admitted by [g], or
      - exists z, p x = z AND x->z is admitted by [g] AND 
                  p is a source-sink path from z to y *)
   Inductive sspath : 'I_#|T| -> 'I_#|T| -> path -> Prop :=
   | sspath_refl (p : path) x : g x (p x) -> sspath x (p x) p
   | sspath_cons (p : path) x y :
       g x (p x) -> 
       sspath (p x) y p ->
       sspath x y p.

  Fixpoint sspath_rec n (x y : 'I_#|T|) : pred path :=
    [pred p : path |
     [|| [&& p x == y & g x (p x)]
       | [&& g x (p x) & if n is n'.+1 then sspath_rec n' (p x) y p
                              else false]]].

  (** We should prove [sspath_pred] equivalent to [sspath] under the assumption 
      that all paths are cycle-free (they can have length no greater than 
      the number of nodes in the graph, #|T|. *)
  Definition sspath_pred (x y : 'I_#|T|) := sspath_rec #|T| x y.

  Notation src i := (source (players i)).
  Notation snk i := (sink (players i)).

  Definition strategy (i : 'I_num_players) :=
    [pred the_path | sspath_pred (src i) (snk i) the_path].

  Definition st : Type := sig (fun f => f \in family [eta strategy]).
  Definition fun_of_st (s : st) : 
  Coercion 

  Definition path_of (s : st) (i : 'I_num_players) : path :=
    the_path (projT2 (s i)). 

  Definition edgeOfPlayer i (s : st) (x y : 'I_#|T|) :=
    path_of s i x == y.

  Definition edgePlayers (s : st) (x y : 'I_#|T|) : pred 'I_num_players :=
    [pred i | edgeOfPlayer i s x y].

  (** The traffic (in number of players) over edge [x],[y] *)
  Definition traffic_edge (s : st) (x y : 'I_#|T|) : nat :=
    #|edgePlayers s x y|.
  
  (** The cost, in st [s], of a particular edge [x],[y]. *)
  Definition cost_edge (s : st) (x y : 'I_#|T|) :=
    ecosts x y (traffic_edge s x y).

  Local Open Scope ring_scope.

  Definition costFun (i : 'I_num_players) (s : st) : rty :=
    \sum_(x : 'I_#|T|)
    \sum_(y : 'I_#|T|)
    if edgeOfPlayer i s x y then cost_edge s x y else 0.

  Instance costFunInstance : CostClass num_players rty strategy_pkg
    := costFun.
  
  Definition phi (s : st) : rty :=
    \sum_(x : 'I_#|T|)
    \sum_(y : 'I_#|T|)
    \sum_(1 <= i < (traffic_edge s x y).+1)
    ecosts x y i.

  Definition movesRel (i : 'I_num_players) : rel strategy_pkg :=
    [fun p p' : strategy_pkg => projT1 p == projT1 p'].
End AtomicRoutingGame.

Instance x rty (T : finType) : CostClass #|T| rty T :=
  @costFun T #|T| _ rty.

Definition atomic_gameMixin : gameMixin strategy_pkg := Game.Mixin moves cost.
Canonical AtomicGame := Eval hnf in GameType strategy_pkg atomic_gameMixin.
  
  Lemma traffic11 (i : 'I_(numplayers AtomicGame)) (x y : 'I_#|T|) t t' :
    Move i t t' ->
    edgeOfPlayer i t' x y ->
    edgeOfPlayer i t x y ->     
    traffic_edge t' x y = traffic_edge t x y.
  Proof.
    rewrite /Move /edgeOfPlayer /=; case /andP=> Hx; move/forallP=> /= H H2 H3.
    rewrite /traffic_edge /edgePlayers /edgeOfPlayer.
    f_equal.
    rewrite /mem /=.
    f_equal.            
    extensionality i0.
    case H4: (i == i0); first by move: (eqP H4)=> <-; rewrite H2 H3.
    have H5: i != i0.
    { apply/negP; move/eqP=> H5; rewrite H5 in H4.
      case: (@eqP _ i0 i0) H4=> //.
    }
    have H6: path_of t i0 = path_of t' i0.
    { move: (eqP ((implyP (H i0)) H5)).
      by rewrite /path_of=> ->.
    }
    by rewrite -H6.
  Qed.    

  Lemma traffic00 (i : 'I_(numplayers AtomicGame)) (x y : 'I_#|T|) t t' :
    Move i t t' ->
    edgeOfPlayer i t' x y = false -> 
    edgeOfPlayer i t x y = false -> 
    traffic_edge t' x y = traffic_edge t x y.
  Proof.
    rewrite /Move /edgeOfPlayer /=; case /andP=> Hx; move/forallP=> /= H H2 H3.    
    rewrite /traffic_edge /edgePlayers /edgeOfPlayer.
    f_equal.
    rewrite /mem /=.
    f_equal.            
    extensionality i0.
    case H4: (i == i0); first by move: (eqP H4)=> <-; rewrite H2 H3.
    have H5: i != i0.
    { apply/negP; move/eqP=> H5; rewrite H5 in H4.
      case: (@eqP _ i0 i0) H4=> //.
    }
    have H6: path_of t i0 = path_of t' i0.
    { move: (eqP ((implyP (H i0)) H5)).
      by rewrite /path_of=> ->.      
    }
    by rewrite -H6.
  Qed.    
  
  Lemma traffic10 (i : 'I_(numplayers AtomicGame)) (x y : 'I_#|T|) t t' :
    Move i t t' ->
    edgeOfPlayer i t' x y -> 
    edgeOfPlayer i t x y = false -> 
    traffic_edge t' x y = (traffic_edge t x y).+1.
  Proof.
    rewrite /Move /edgeOfPlayer /=; case /andP=> Hx; move/forallP=> /= H H2 H3.        
    rewrite /traffic_edge.
    rewrite (cardD1x (j:=i))=> //.
    rewrite /addn /=.
    f_equal.
    rewrite /edgePlayers.
    apply: eq_card=> j.
    rewrite /in_mem /=.
    case H4: (j == i)=> /=.
    move: (eqP H4)=> ->.
    by rewrite /edgeOfPlayer H2 H3 andbC.
    have H5: (i != j).
    { by apply/negP=> H5; move: (eqP H5)=> H6; rewrite H6 eq_refl in H4.
    }
    move: (implyP (H j)); move/(_ H5)/eqP=> H6.
    rewrite /edgeOfPlayer /path_of H6.
    by rewrite andbC.
  Qed.    

  Lemma traffic01 (i : 'I_(numplayers AtomicGame)) (x y : 'I_#|T|) t t' :
    Move i t t' ->
    edgeOfPlayer i t' x y = false -> 
    edgeOfPlayer i t x y -> 
    (traffic_edge t' x y).+1 = traffic_edge t x y.
  Proof.
    rewrite /Move /edgeOfPlayer /=; case /andP=> Hx; move/forallP=> /= H H2 H3.            
    rewrite /traffic_edge.
    symmetry.
    rewrite (cardD1x (j:=i))=> //.
    rewrite /addn /=.
    f_equal.
    rewrite /edgePlayers.
    apply: eq_card=> j.
    rewrite /in_mem /=.
    case H4: (j == i)=> /=.
    move: (eqP H4)=> ->.
    by rewrite /edgeOfPlayer H2 H3 andbC.
    have H5: (i != j).
    { by apply/negP=> H5; move: (eqP H5)=> H6; rewrite H6 eq_refl in H4.
    }
    move: (implyP (H j)); move/(_ H5)/eqP=> H6.
    rewrite /edgeOfPlayer /path_of H6.
    by rewrite andbC.
  Qed.    

  Lemma subr_xx (x : rty) : x - x = 0.
  Proof.
    suff: x - x == 0; first by move/eqP=> <-.
    by rewrite subr_eq0; apply/eqP.
  Qed.

  Lemma sum_add1 (f : nat -> rty) m (Hpos : (0 < m)%N) : 
    \sum_(1 <= i < m.+1) f i - \sum_(1 <= i < m) f i = f m.
  Proof.
    rewrite big_nat_recl=> //.
    rewrite -addrA -sumrB telescope_sumr=> //.
    by rewrite addrA [f (S O) + _]addrC -addrA subr_xx addr0.
  Qed.                               
    
  Lemma sum_sub1 (f : nat -> rty) m (Hpos : (0 < m)%N) : 
    \sum_(1 <= i < m) f i - \sum_(1 <= i < m.+1) f i = - f m.
  Proof.
    rewrite addrC.
    rewrite big_nat_recl=> //.
    rewrite opprD.
    rewrite -addrA.
    suff H: -f 1%N + -(-(\sum_(1 <= i < m) f i - \sum_(1 <= i < m) f i.+1)) = -f m.
    { rewrite opprK in H.
      by rewrite -H; f_equal; rewrite addrC.
    }
    rewrite -sumrB addrC raddf_sum /=.
    suff H: - (\sum_(1 <= i < m) (f i.+1 - f i)) - f 1%N = - f m.
    { rewrite -H.
      f_equal.
      f_equal.
      f_equal.
      extensionality i.
      f_equal.
      by rewrite opprB.
    }
    rewrite telescope_sumr=> //.
    by rewrite opprB addrC addrA [-f _ + _]addrC subr_xx sub0r. 
  Qed.    

  Lemma phi_exact (i : 'I_(numplayers AtomicGame)) (t t' : st) :
    Move i t t' -> 
    phi t' - phi t = cost i t' - cost i t.
  Proof.
    move=> H.
    rewrite /phi /cost.
    rewrite -!sumrB; simpl.
    f_equal.
    extensionality x.
    f_equal.
    rewrite -!sumrB.
    f_equal.
    extensionality y.
    f_equal.
    rewrite /cost_edge.
    case Ht': (edgeOfPlayer i t' x y); case Ht: (edgeOfPlayer i t x y).
    { (*true, true*)
      rewrite (traffic11 H Ht' Ht).
      rewrite -sumrB.
      rewrite subr_xx.
      rewrite sumrB.
      by rewrite subr_xx.
    }
    { (*true, false*)
      rewrite (traffic10 H Ht' Ht).
      move: (traffic_edge _ _ _)=> n.
      move Hecosts: (ecosts x y)=> f.
      move Hm: (n.+1)=> m.
      rewrite sum_add1.
      by rewrite subr0.
      by rewrite -Hm.
    }
    { (*false, true*)
      rewrite (traffic01 H Ht' Ht).
      case Hn: (traffic_edge _ _ _)=> [|n].
      { rewrite /traffic_edge in Hn.
        rewrite (cardD1x (j:=i)) in Hn=> //.
      }
      move Hecosts: (ecosts x y)=> f.
      rewrite sum_sub1=> //.
      by rewrite sub0r.
    }
    rewrite subr0.
    rewrite (traffic00 H Ht' Ht).
    by rewrite subr_xx.
  Qed.

  Instance atomic_Potential : Potential (T:=AtomicGame) :=
    mkPotential phi_exact.
End AtomicRoutingGame.  

  
  
      
  
  
  
  
  
  
                             