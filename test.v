Inductive even : nat -> Prop :=
| EO : even O
| ESS : forall n : nat, even n -> even (S (S n)).

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_even :
  forall n : nat, even (double n).
Proof.