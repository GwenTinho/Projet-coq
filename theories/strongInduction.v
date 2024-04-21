(*Adapted from https://github.com/tchajed/strong-induction/blob/master/StrongInduction.v*)

Require Import PeanoNat.

  Theorem strong_induction : forall P : nat -> Set, forall IH : forall m, (forall n, n < m -> P n) -> P m, forall p, P p.
  Proof.
    intros P IH p.
    assert ( forall n,
               (forall m, m <= n -> P m)).
    {
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
        apply le_S_n.
        apply Nat.le_trans with m; assumption.
    }
    induction p.
    - apply IH.
      intros n H0.
      apply Nat.nlt_0_r in H0.
      contradiction.
    - apply H with (n := S p).
      apply Nat.le_refl.
  Defined.

