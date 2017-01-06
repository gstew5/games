Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Section AtomicRoutingGame.
  Variable T : finType. (** The type of nodes *)
  Variable num_players : nat. (** The number of players *)
  Variable e : rel T.   (** The graph's edges *)

  Let g := rgraph e.    (** The graph induced by [e] *)

  Variable rty : realFieldType.
  (** Edge costs are modeled by a function mapping 
        - node i  : T    The source node for this edge
        - node j  : T    The target node for this edge
        - traffic : nat  The amount of traffic over this edge
      to a real number type [rty]. *)
  Variable ecosts : T -> T -> nat -> rty.

  (** Players are pairs of source-sink vertices. *)
  Record player : Type :=
    mkPlayer {
        source : T;
        sink : T
      }.
  Variable players : 'I_num_players -> player.

  (** A source-sink path from [x] to [y] is a path in [e] from [x]
      with last node equal [y]. *)
  Definition sspath (x y : T) : pred (seq T) :=
    [pred p : seq T | [&& path e x p & y == last x p]].

  Notation src i := (source (players i)).
  Notation snk i := (sink (players i)).

  (** We explode the [strategy] type to a get a free [eqType] instance. *)
  Definition strategy (i : 'I_num_players) :=
    sig (fun the_path => sspath (src i) (snk i) the_path).
  Definition mkStrategy
             (i : 'I_num_players)
             (the_path : seq T)
             (path_valid : sspath (src i) (snk i) the_path) : strategy i :=
    exist (fun the_path => sspath (src i) (snk i) the_path) the_path path_valid.
  Definition the_path (i : 'I_num_players) (s : strategy i) : seq T := projT1 s.
  Definition path_valid (i : 'I_num_players) (s : strategy i) := projT2 s.

  (** A state maps players to strategies. *)
  Definition state := forall i : 'I_num_players, strategy i.

  (** A move is valid for [i] as long as it doesn't screw around with the 
      strategies selected by other players. (Player [i] can choose any 
      strategy it likes -- the choice is nondeterministic.) *)
  Definition moves (i : 'I_num_players) : rel state :=
    fun s s' : state => [forall j : 'I_num_players, (i != j) ==> (s j == s' j)].

  (** Does path [p] contain edge [x],[y]? *)
  Fixpoint edge_in (p : seq T) (x y : T) :=
    if p is x' :: p' then
      if p' is y' :: _ then [|| [&& x == x' & y == y'] | edge_in p' x y]
      else false
    else false.

  (** The traffic (in number of players) over edge [x],[y] *)
  Definition traffic_edge (s : state) (x y : T) : nat :=
    \sum_(i : 'I_num_players) (if edge_in (the_path (s i)) x y then 1 else O).
  
  (** The cost, in state [s], of a particular edge [x],[y]. *)
  Definition cost_edge (s : state) (x y : T) :=
    ecosts x y (traffic_edge s x y).

  Local Open Scope ring_scope.
  
  Definition cost (s : state) : rty :=
    \sum_(x : T) (\sum_(y : T) (cost_edge s x y)).
End AtomicRoutingGame.  
  
  
      
  
  
  
  
  
  
                             