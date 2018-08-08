Require Import Classical Omega.

Parameter A B C : Prop.

Lemma bleh : (B -> C) <-> ((A /\ B) -> (A /\ C)).
Proof.
  split.
  intros.
  destruct H0. apply H in H1. split. exact H0. exact H1.
  intros.
  