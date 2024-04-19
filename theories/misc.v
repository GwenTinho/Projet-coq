From LIDec Require Import base.
Require Import List.

Import ListNotations.

Lemma rev_bij : forall A, forall l r : list A, l = r <-> rev l = rev r.
Proof.
  intros A l r.
  split.
  - intro H. congruence.
  - intro H.
    specialize  (@f_equal (list A) (list A) (@rev A)) as Hrev.
    apply Hrev in H.
    repeat rewrite rev_involutive in H.
    assumption.
Qed.


Lemma app_inv_tail : forall A, forall l l' r : list A, l ++ r = l' ++ r -> l = l'.
Proof.
  intros A l l' r H.
  rewrite rev_bij in H.
  repeat rewrite rev_app_distr in H.
  apply app_inv_head in H.
  rewrite <- rev_bij in H.
  assumption.
Qed.




  Lemma weird_left : forall A B, notT (B ∧ A = A).
  Proof.
    intros A B H.
    induction A
    ; inversion H.
    apply IHA2.
    rewrite H1.
    assumption.
  Qed.

  Lemma weird_right : forall A B, notT (A ∧ B = A).
  Proof.
    intros A B H.
    induction A; inversion H.
    apply IHA1.
    rewrite H2.
    assumption.
  Qed.

  Lemma weird_or_left : forall A B, notT (B ∨ A = A).
  Proof.
    intros A B H.
    induction A; inversion H.
    apply IHA2.
    rewrite H1.
    assumption.
  Qed.


  Lemma weird_or_right : forall A B, notT (A ∨ B = A).
  Proof.
    intros A B H.
    induction A; inversion H.
    apply IHA1.
    rewrite H2.
    assumption.
  Qed.
