From LIDec Require Import base.
From LIDec Require Import listSplitting.
From LIDec Require Import misc.
Require Import List.

Import ListNotations.

Section ElimRules.

  Variable S : sequent.

  Let Γ : list formula := let '(Γ ⊢? A) := S in Γ.

  Let A : formula := let '(Γ ⊢? A) := S in A.

  Variable IH : forall Γ' A',
      deg_sequent (Γ' ⊢? A') < deg_sequent (Γ ⊢? A) -> (Γ' ⊢ A') + { notT (Γ' ⊢ A') }.

  (* Cette section a pour but de prouver le (gros) lemme suivant.
     Ne pas hésiter à écrire des lemmes intermédiaires auparavant
     pour vérifier l’applicabilité de chaque règle. *)





Lemma provable_with_IE_bot :
  (Γ ⊢ A) + { forall (p : LI S),
        match p return Prop with IE_bot => False | _ => True end }.
Proof.
  destruct (in_dec_formula ⊥ Γ) as [bot_in_gamma | bot_nin_gamma].
  - left. apply in_split_formula in bot_in_gamma.
    destruct bot_in_gamma as [(pre, post) eq].
    simpl in eq.
    rewrite eq.
    apply IE_bot.
  - right. intro p.
    assert (let '(Γ ⊢? A) := S in ~ In ⊥ Γ) as bot_nin_ctx_S.
    {
      destruct S. assumption.
    }
    destruct p; trivial.
    apply bot_nin_ctx_S.
    apply in_or_app.
    right.
    apply in_or_app.
    left.
    simpl.
    auto.
Defined.



Ltac s_struct := assert (S = (Γ ⊢? A)) as S_struct; try (destruct S; reflexivity).

Definition Q_and (A : formula)  (l0 : list formula) (A0 : formula) (l1 : list formula) :=
 (forall B C, A0 = B ∧ C -> notT (l0 ++ [B;C] ++ l1 ⊢ A)).

Lemma f_and : forall  l0 A0 l1, l0 ++ [A0] ++ l1= Γ -> (Γ ⊢ A) + {Q_and A l0 A0 l1}.
Proof.
  intros l0 A0 l1 eq.

  unfold Q_and.
  specialize (decidable_and A0) as [[[B C] eq0] | Neg].
  - 
    specialize (deg_IE_and l0 B C l1 A) as Deg.
    rewrite eq0 in eq.
    rewrite <- eq in IH.
    apply IH in Deg.
    destruct Deg as [L | R].
    + rewrite <- eq.
      left.
      apply IE_and.
      assumption.
    + right.
      destruct S.
      intros B0 C0 H.
      rewrite H in eq0.
      inversion eq0.
      subst.
      assumption.
  - right.
    destruct S.
    intros B C H N.
    specialize (Neg B C).
    contradiction.
Defined.

Lemma pre_IE_and : (Γ ⊢ A) + {
      forall l0 A0 l1, l0 ++ [A0] ++ l1 = Γ -> Q_and A l0 A0 l1}.
Proof.
  specialize (list_split_ind  formula (Γ ⊢ A)  (Q_and A) Γ f_and) as [Fine | NotFine].
  - left. assumption.
  - right.
    intros l0 A0 l1 H.
    apply NotFine.
    assumption.
Defined.
  

Lemma provable_with_IE_and :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_and _ => False
        | _ => True
        end
  }.
Proof.
  specialize pre_IE_and as [Done | Workie].
  -  left. assumption.
  - right.
    s_struct.
    destruct p; trivial.
    unfold Q_and in Workie.
    specialize (Workie Γ0 (A0 ∧ B) Γ').
    simpl in Workie.
    assert (Γ = Γ0 ++ [A0 ∧ B] ++ Γ').
    {
      auto.
    }
    symmetry in H.
    simpl in H.
    apply (Workie H A0 B).
    + reflexivity.
    + simpl in p.
      assumption.
Defined.





Definition Q_or (A : formula)  (l0 : list formula) (A0 : formula) (l1 : list formula) :=
  (forall B C, A0 = (B ∨ C) -> ( notT (l0 ++ [B] ++ l1 ⊢ A)) \/ ( notT  (l0 ++ [C] ++ l1 ⊢ A) )).

Lemma f_or : forall  l0 A0 l1, l0 ++ [A0] ++ l1= Γ -> (Γ ⊢ A) + { Q_or A l0 A0 l1 }.
Proof.
  intros l0 A0 l1 eq.
  unfold Q_or.
  specialize (decidable_or A0) as [[[B C] eq0] | Neg].
  - specialize (deg_IE_or_left l0 B C l1 A) as Deg_left.
    specialize (deg_IE_or_right l0 B C l1 A) as Deg_right.
    rewrite eq0 in eq.
    rewrite <- eq in IH.
    apply IH in Deg_left, Deg_right.
    destruct Deg_left as [L | R]; destruct Deg_right as [LL | RR].
    + rewrite <- eq.
      left.
      apply IE_or; assumption.
    + right.
      destruct S.
      intros B0 C0 H.
      right.
      rewrite H in eq0.
      inversion eq0.
      subst.
      assumption.
    + right.
      intros B0 C0 H.
      subst.
      inversion H.
      left.
      rewrite <- H1.
      assumption.
    + right.
      intros B0 C0 H.
      subst.
      inversion H.
      subst.
      left.
      assumption.
  - right.
    intros B C H.
    subst.
    specialize (Neg B C) as K.
    contradiction.
Defined.

Lemma pre_IE_or : (Γ ⊢ A) + {
      forall l0 A0 l1, l0 ++ [A0] ++ l1 = Γ -> Q_or A l0 A0 l1}.
Proof.
  specialize (list_split_ind  formula (Γ ⊢ A)  (Q_or A) Γ f_or) as [Fine | NotFine].
  - left. assumption.
  - right.
    intros l0 A0 l1 H.
    apply NotFine.
    assumption.
Defined.

  

  

Lemma provable_with_IE_or :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_or _  _ => False
        | _ => True
        end
  }.
Proof.
  specialize pre_IE_or as [Done | Workie].
  -  left. assumption.
  - right.
    s_struct.
    destruct p; trivial.
    unfold Q_or in Workie.
    specialize (Workie Γ0 (A0 ∨ B) Γ').
    simpl in Workie.
    assert (Γ = Γ0 ++ [A0 ∨ B] ++ Γ').
    {
      auto.
    }
    symmetry in H.
    simpl in H.
    specialize (Workie H A0 B).
    assert (A0 ∨ B = A0 ∨ B).
    { reflexivity. }
    apply Workie in H0.
    destruct H0 as [L | R].
    + apply L. simpl in p1. assumption.
    + apply R. simpl in p2. assumption.
Defined.



Definition Q_impl_and (A : formula)  (l0 : list formula) (A0 : formula) (l1 : list formula) :=
  (forall B C D, A0 = ((B ∧ C) ⇒ D )-> notT (l0 ++ [B ⇒ C ⇒ D] ++ l1 ⊢ A)).

Lemma f_impl_and : forall  l0 A0 l1, l0 ++ [A0] ++ l1= Γ -> (Γ ⊢ A) + { Q_impl_and A l0 A0 l1 }.
Proof.
  intros l0 A0 l1 eq.
  unfold Q_impl_and.
  specialize (decidable_impl_and A0) as [[[[B C] D] eq0] | Neg].
  - specialize (deg_IE_impl_and l0 B C D l1 A) as Deg.
    rewrite eq0 in eq.
    rewrite <- eq in IH.
    apply IH in Deg.
    destruct Deg as [L | R].
    + rewrite <- eq.
      left.
      apply IE_impl_and; assumption.
    + right.
      destruct S.
      intros B0 C0 D0 H.
      rewrite H in eq0.
      inversion eq0.
      subst.
      assumption.
  - right.
    intros B C D H.
    subst.
    specialize (Neg B C D) as K.
    contradiction.
Defined.

Lemma pre_IE_impl_and : (Γ ⊢ A) + {
      forall l0 A0 l1, l0 ++ [A0] ++ l1 = Γ -> Q_impl_and A l0 A0 l1}.
Proof.
  specialize (list_split_ind  formula (Γ ⊢ A)  (Q_impl_and A) Γ f_impl_and) as [Fine | NotFine].
  - left. assumption.
  - right.
    intros l0 A0 l1 H.
    apply NotFine.
    assumption.
Defined.

Lemma provable_with_IE_impl_and :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_impl_and _ => False
        | _ => True
        end
  }.
Proof.
  specialize pre_IE_impl_and as [Done | Workie].
  -  left. assumption.
  - right.
    s_struct.
    destruct p; trivial.
    unfold Q_impl_and in Workie.
    specialize (Workie Γ0 ((A0 ∧ B) ⇒ C) Γ').
    simpl in Workie.
    assert (Γ = Γ0 ++ [(A0 ∧ B) ⇒ C] ++ Γ').
    {
      auto.
    }
    symmetry in H.
    simpl in H.
    apply (Workie H A0 B C).
    + reflexivity.
    + simpl in p.
      assumption.
Defined.

Definition Q_impl_or (A : formula)  (l0 : list formula) (A0 : formula) (l1 : list formula) :=
  (forall B C D, A0 = ((B ∨ C) ⇒ D )-> notT (l0 ++ [B ⇒ D] ++ [C ⇒ D] ++ l1 ⊢ A)).

Lemma f_impl_or : forall  l0 A0 l1, l0 ++ [A0] ++ l1= Γ -> (Γ ⊢ A) + { Q_impl_or A l0 A0 l1 }.
Proof.
  intros l0 A0 l1 eq.
  unfold Q_impl_or.
  specialize (decidable_impl_or A0) as [[[[B C] D] eq0] | Neg].
  - specialize (deg_IE_impl_or l0 B C D l1 A) as Deg.
    rewrite eq0 in eq.
    rewrite <- eq in IH.
    apply IH in Deg.
    destruct Deg as [L | R].
    + rewrite <- eq.
      left.
      apply IE_impl_or; assumption.
    + right.
      destruct S.
      intros B0 C0 D0 H.
      rewrite H in eq0.
      inversion eq0.
      subst.
      assumption.
  - right.
    intros B C D H.
    subst.
    specialize (Neg B C D) as K.
    contradiction.
Defined.

Lemma pre_IE_impl_or : (Γ ⊢ A) + {
      forall l0 A0 l1, l0 ++ [A0] ++ l1 = Γ -> Q_impl_or A l0 A0 l1}.
Proof.
  specialize (list_split_ind formula (Γ ⊢ A)  (Q_impl_or A) Γ f_impl_or) as [Fine | NotFine].
  - left. assumption.
  - right.
    intros l0 A0 l1 H.
    apply NotFine.
    assumption.
Defined.

Lemma provable_with_IE_impl_or :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_impl_or _ => False
        | _ => True
        end
  }.
Proof.
  specialize pre_IE_impl_or as [Done | Workie].
  -  left. assumption.
  - right.
    s_struct.
    destruct p; trivial.
    unfold Q_impl_or in Workie.
    specialize (Workie Γ0 ((A0 ∨ B) ⇒ C) Γ').
    simpl in Workie.
    assert (Γ = Γ0 ++ [(A0 ∨ B) ⇒ C] ++ Γ').
    {
      auto.
    }
    symmetry in H.
    simpl in H.
    apply (Workie H A0 B C).
    + reflexivity.
    + simpl in p.
      assumption.
Defined.

Definition Q_impl_impl (A : formula)  (l0 : list formula) (A0 : formula) (l1 : list formula) :=
  (forall B C D, A0 = ((B ⇒  C) ⇒ D )-> notT (l0 ++ [B; C ⇒ D] ++ l1 ⊢ A)).

Lemma f_impl_impl : forall  l0 A0 l1, l0 ++ [A0] ++ l1= Γ -> (Γ ⊢ A) + { Q_impl_impl A l0 A0 l1 }.
Proof.
  intros l0 A0 l1 eq.
  unfold Q_impl_impl.
  specialize (decidable_impl_impl A0) as [[[[B C] D] eq0] | Neg].
  - specialize (deg_IE_impl_impl_left l0 B C D l1 A) as Deg_left.
    specialize (deg_IE_impl_impl_right l0 B C D l1 A) as Deg_right.
    rewrite eq0 in eq.
    rewrite <- eq in IH.
    apply IH in Deg_left, Deg_right.
    destruct Deg_left as [L | R]; destruct Deg_right as [LL | RR].
    + rewrite <- eq.
      left.
      apply IE_impl_impl; assumption.
    + right.
      intros B0 C0 D0 H.
      rewrite H in eq0.
      inversion eq0.
      subst.
      admit.
    + right.
      intros B0 C0 D0 H.
      subst.
      inversion H.
      subst.
      admit.
    + admit.
  - right.
    intros B C D H.
    subst.
    specialize (Neg B C D) as K.
    contradiction.
Admitted.


Lemma pre_IE_impl_impl : (Γ ⊢ A) + {
      forall l0 A0 l1, l0 ++ [A0] ++ l1 = Γ -> Q_impl_impl A l0 A0 l1}.
Proof.
  specialize (list_split_ind  formula (Γ ⊢ A)  (Q_impl_impl A) Γ f_impl_impl) as [Fine | NotFine].
  - left. assumption.
  - right.
    intros l0 A0 l1 H.
    apply NotFine.
    assumption.
Defined.

Lemma provable_with_IE_impl_impl :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_impl_impl _ _ => False
        | _ => True
        end
  }.
Proof.
  specialize pre_IE_impl_impl as [Done | Workie].
  -  left. assumption.
  - right.
    s_struct.
    destruct p; trivial.
    unfold Q_impl_impl in Workie.
    specialize (Workie Γ0 ((A0 ⇒ B) ⇒ C) Γ').
    simpl in Workie.
    assert (Γ = Γ0 ++ [(A0 ⇒ B) ⇒ C] ++ Γ').
    {
      auto.
    }
    symmetry in H.
    simpl in H.
    apply (Workie H A0 B C).
    + reflexivity.
    + admit.
Admitted.


(*
Lemma pre_IE_impl_left : (Γ ⊢ A) + {
      forall l0 A0 l1, l0 ++ [A0] ++ l1 = Γ -> Q_impl_left A l0 A0 l1}.
Proof.
  specialize (list_split_ind  formula (Γ ⊢ A)  (Q_impl_left A) Γ f_impl_left) as [Fine | NotFine].
  - left. assumption.
  - right.
    intros l0 A0 l1 H.
    apply NotFine.
    assumption.
Defined.
*)

Lemma provable_with_IE_impl_left :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_impl_left _ _ => False
        | _ => True
        end
  }.
Proof.

Admitted.


End ElimRules.


