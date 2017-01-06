Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema.
  
Section Hex.
  (** Dimensionality of the game (number of players) *)
  Variable n : nat.
  Notation N := (n.+2). (** We require at least 2 players. *)

  (** Size of the board *)
  Variable k : nat.
  Notation K := (k.+1). (** The size must be positive *)  

  (** We label players i \in [0..N). *)
  Notation player := ('I_N).
  
  (** A board position (or vertex) is an N.-tuple of integers in [1..K]. *)
  Definition posval : Type := sig (fun i : 'I_K.+1 => 1 <= i).
  Coercion posval2val (p : posval) : 'I_K.+1 := projT1 p.
  Definition pos := N.-tuple posval.  

  (** 1 \in [1..K] *)
  Program Definition ord1 : 'I_K.+1 := @Ordinal K.+1 1 _.

  (** A position "x" is less than a position "y" if 
      [x i <= y i] for all i \in [0..N). *)
  Definition leq (x y : pos) : bool :=
    [forall i : player, tnth x i <= tnth y i].

  (** Two positions are comparable if: 
      - They're not equal, and 
      - One is less than the other. *)
  Definition comparable (x y : pos) : bool :=
    [&& x != y & [|| leq x y | leq y x]].  

  Lemma comparable_sym x y : comparable x y -> comparable y x.
  Proof.
    case/andP=> H; case/orP=> H2.
    { apply/andP; split; first by apply/eqP=> H3; rewrite -H3 eqxx in H.
      by apply/orP; right. }
    apply/andP; split; first by apply/eqP=> H3; rewrite -H3 eqxx in H.
    by apply/orP; left.
  Qed.
    
  (** Two positions are adjacent if they're exactly radius 1 from each
      other (and they avoid the forbidden diagonal, positive or negative
      depending on how you view the board). *)

  Section max.
    Local Open Scope ring_scope.
    (** This is the max difference at any position i. 
        We inject into rationals here because of the way [max] is defined. *)
    Definition max_diff (x y : pos) : rat :=
      max xpredT (fun i : player => (tnth x i - tnth y i)%:R) ord0.

    Definition adjacent (x y : pos) : bool :=
      [&& max_diff x y == 1%:R & comparable x y].
  End max.

  (** A labeling of the game board maps vertices z = (z_1, z_2, ..., z_N) to
      "player" labels in [0..N). We represent this map 
      as a finite function (a function with finite domain) from the 
      space of vertices to the space of player labels. *)
  Definition labeling := {ffun pos -> player}.

  (** The "winning" sets for player i: *)
  Definition winning_start (i : player) : pred pos :=
    [pred x : pos | posval2val (tnth x i) == ord1].
  Definition winning_end (i : player) : pred pos :=
    [pred x : pos | posval2val (tnth x i) == ord_max].
  
  (** A "prepath" is a sequence of board positions. *)
  Definition prepath := (seq pos)%type.

  (** [path_pred startx endx] defines (possibly empty) tails of paths
      from [startx] to [endx]. *)
  Inductive path_pred (startx endx : pos) : prepath -> Prop :=
  | path_one :
      startx = endx -> 
      path_pred startx endx [::]
  | path_cons y l :
      adjacent startx y ->
      path_pred y endx l ->
      path_pred startx endx [:: y & l].

  (** An "ok_path" is a nonempty prepath with first node startx, 
      with tail satisfying [path_pred startx endx]. *)
  Definition ok_path (startx endx : pos) (l : prepath) : Prop :=
    if l is [:: y & l] then startx = y /\ path_pred startx endx l
    else False.
  
  (** We explode path as a Sigma type to get free eqType and finType
      instances. *)  
  Definition path (startx endx : pos) : Type :=
    sig (fun l => ok_path startx endx l). 
  Section PathConstructors.
    Variables startx endx : pos.
    Definition mkPath (l : prepath) (pf : ok_path startx endx l)
      : path startx endx :=
      exist (fun l => ok_path startx endx l) l pf.
    Definition the_path (l : path startx endx) : prepath := projT1 l.
    Definition the_path_pred (l : path startx endx)
      : ok_path startx endx (the_path l) := projT2 l.
  End PathConstructors.  

  (** An "player_path" is a path in which all positions are marked "i". *)
  Definition player_path
             (i : player) (startx endx : pos)
             (b : labeling) : pred (path startx endx) :=
    [pred l : path startx endx |
     [&& winning_start i startx
       , winning_end i endx
       & [forall x : pos, (x \in the_path l) ==> (b x == i)]]].

  Theorem Hex :
    forall b : labeling, 
    exists (startx endx : pos) (l : path startx endx) (i : player),
      player_path i b l.
  Admitted. (*TODO*)            
End Hex.