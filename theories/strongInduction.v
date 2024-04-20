(*Adapted from https://github.com/tchajed/strong-induction/blob/master/StrongInduction.v*)

Require Import PeanoNat.
Require Import ZArith Psatz.

Section StrongInduction.

  Variable P:nat -> Set.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.


  Hint Resolve le_S_n.

  (** * Strengthen the induction hypothesis. *)

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    intro n.
    induction n.
    - intros m H.
      rewrite Nat.le_0_r in H.
      apply IH.
      intros n H0.
      subst.
      apply Nat.nlt_0_r in H0.
      contradiction.
    - intros m H.
      apply IH.
      intros n0 H0.
      apply IHn.
      lia.
  Defined.

  Theorem strong_induction : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Defined.

End StrongInduction.
