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



Definition Q_impl_top (A : formula)  (l0 : list formula) (A0 : formula) (l1 : list formula) :=
 forall B, (A0 = (⊤ ⇒ B )-> notT (l0 ++ [B] ++ l1 ⊢ A)).

Lemma f_impl_top : forall  l0 A0 l1, l0 ++ [A0] ++ l1= Γ -> (Γ ⊢ A) + { Q_impl_top A l0 A0 l1 }.
Proof.
  intros l0 A0 l1 eq.
  unfold Q_impl_top.
  specialize (decidable_impl_top A0) as [[B eq0] | Bad].
  -  specialize (deg_IE_impl_top l0 B l1 A) as Deg.
    rewrite eq0 in eq.
    rewrite <- eq in IH.
    apply IH in Deg.
    destruct Deg as [L | R].
    + rewrite <- eq.
      left.
      apply IE_impl_top; assumption.
    + right.
      destruct S.
      intros B0 H.
      subst.
      inversion H.
      congruence.
  - right.
    intros B H N.
    apply (Bad B).
    assumption.
Defined.

Lemma pre_IE_impl_top : (Γ ⊢ A) + {
      forall l0 A0 l1, l0 ++ [A0] ++ l1 = Γ -> Q_impl_top A l0 A0 l1}.
Proof.
  specialize (list_split_ind  formula (Γ ⊢ A)  (Q_impl_top A) Γ f_impl_top) as [Fine | NotFine].
  - left. assumption.
  - right.
    intros l0 A0 l1 H.
    apply NotFine.
    assumption.
Defined.

Lemma provable_with_IE_impl_top :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_impl_top _ => False
        | _ => True
        end
  }.
Proof.
  specialize pre_IE_impl_top as [Done | Workie].
  -  left. assumption.
  - right.
    s_struct.
    destruct p; trivial.
    unfold Q_impl_top in Workie.
    specialize (Workie Γ0 (⊤ ⇒ A0)  Γ').
    assert (Γ0 ++ [⊤ ⇒ A0] ++ Γ' = Γ).
    { auto. }
    specialize (Workie H A0).
    apply Workie.
    + reflexivity.
    + auto.
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
  (forall B C D, A0 = ((B ⇒  C) ⇒ D )-> notT (l0 ++ [B; C ⇒ D] ++ l1 ⊢ C) \/ notT (l0 ++ [D] ++ l1 ⊢ A)).

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
      right. assumption.
    + right.
      intros B0 C0 D0 H.
      subst.
      inversion H.
      left. congruence.
    + right. intros B0 C0 D0 H.
      subst.
      inversion H.
      right.
      rewrite <- H3.
      assumption.
  - right.
    intros B C D H.
    subst.
    specialize (Neg B C D) as K.
    contradiction.
Defined.


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
    specialize (Workie H A0 B C) as K.
    assert ( (A0 ⇒ B) ⇒ C = (A0 ⇒ B) ⇒ C).
    {reflexivity. }
    apply Workie in H0.
    + destruct H0 as [L | R].
      * apply L. simpl in p1. assumption.
      * apply R. simpl in p2. assumption.
    + assumption.
Defined.


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
(*Idea : Same setup as for the others, but in two steps, first implement Q_impl*)

Definition Q_impl_left (A : formula)  (l1 : list formula) (A0 : formula) (l2 : list formula) :=
  (forall l r B C , A0 = (B ⇒  C ) -> (l1 = l ++ [B] ++ r) -> notT (l ++ [B] ++ r ++ [C] ++ l2 ⊢ A)).


Lemma f_impl_left : forall  l0 A0 l1, l0 ++ [A0] ++ l1= Γ -> (Γ ⊢ A) + { Q_impl_left A l0 A0 l1 }.
Proof.
  intros l0 A0 l1 eq.
  unfold Q_impl_left.
  specialize (decidable_impl A0) as [[[B C] eq0] | Neg].
  specialize (in_dec_formula B l0) as [Bin | Bnin].
  - apply in_split_formula in Bin.
    destruct Bin as [[l r] eq1].
    simpl in eq1.
    specialize (deg_IE_impl_left l B r C l1 A) as Deg.
    rewrite eq0 in eq.
    rewrite eq1 in eq.
    rewrite <- eq in IH.
    assert (l ++ [B] ++ r ++ [B ⇒ C] ++ l1 = (l ++ B :: r) ++ [B ⇒ C] ++ l1 ).
    {
      repeat rewrite <- app_assoc.
      reflexivity.
    }
    rewrite <- H in IH.
    apply IH in Deg.
    destruct Deg as [L | R].
    + rewrite <- eq.
      left.
      rewrite <- H.
      apply IE_impl_left; assumption.
    + right.
      destruct S.
      intros l2 r0 B0 C0 H0.
      rewrite H0 in eq0.
      inversion eq0.
      subst.
      intro eq1.
      assert (l ++ [B] ++ r ++ [C] ++ l1 = l2 ++ [B] ++ r0 ++ [C] ++ l1).
      {
        simpl.
        simpl in eq1.
        assert (l ++ B :: r ++ C :: l1 = (l ++ B :: r) ++ C :: l1).
        {
          rewrite <- app_assoc.
          reflexivity.
        }
        rewrite H0.
        rewrite eq1.
        rewrite <- app_assoc.
        reflexivity.
      }
      rewrite <- H0.
      assumption.
  - right.
    intros l r B0 C0 H H0.
    subst.
    inversion H.
    subst.
    intro N.
    apply Bnin.
    apply in_or_app.
    right.
    simpl.
    left. reflexivity.
  - right.
    intros l r B C H H0 N.
    apply (Neg B C).
    assumption.
Defined.


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


Lemma provable_with_IE_impl_left :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_impl_left _ => False
        | _ => True
        end
  }.
Proof.
  specialize pre_IE_impl_left as [Done | Workie].
  -  left. assumption.
  - right.
    s_struct.
    destruct p; trivial.
    unfold Q_impl_left in Workie.
    specialize (Workie (Γ0 ++ [A0] ++ Γ') (A0 ⇒ B) Γ'').
    assert ((Γ0 ++ [A0] ++ Γ') ++ [A0 ⇒ B] ++ Γ'' = Γ).
    {
      repeat rewrite <- app_assoc.
      auto.
    }
    apply (Workie H Γ0 Γ' A0 B); try reflexivity.
    auto.
Defined.

Definition Q_impl_right (A : formula)  (l1 : list formula) (A0 : formula) (l2 : list formula) :=
  (forall l r B C , A0 = (B ⇒  C ) -> (l2 = l ++ [B] ++ r) -> notT (l1 ++ [C] ++ l ++ [B] ++ r ⊢ A)).


Lemma f_impl_right : forall  l0 A0 l1, l0 ++ [A0] ++ l1= Γ -> (Γ ⊢ A) + { Q_impl_right A l0 A0 l1 }.
Proof.
  intros l0 A0 l1 eq.
  unfold Q_impl_right.
  specialize (decidable_impl A0) as [[[B C] eq0] | Neg].
  specialize (in_dec_formula B l1) as [Bin | Bnin].
  - apply in_split_formula in Bin.
    destruct Bin as [[l r] eq1].
    simpl in eq1.
    specialize (deg_IE_impl_right l0 B l C r A) as Deg.
    rewrite eq0 in eq.
    rewrite eq1 in eq.
    rewrite <- eq in IH.
    simpl in Deg, IH.
    apply IH in Deg.
    destruct Deg as [L | R].
    + rewrite <- eq.
      left.
      apply IE_impl_right; assumption.
    + right.
      intros l2 r0 B0 C0 H H0.
      subst.
      inversion H.
      subst.
      simpl in *.
      rewrite <- H0.
      assumption.
  - right.
    intros l r B0 C0 H H0.
    subst.
    inversion H.
    subst.
    intro N.
    apply Bnin.
    apply in_or_app.
    right.
    simpl.
    left. reflexivity.
  - right.
    intros l r B C H H0 N.
    apply (Neg B C).
    assumption.
Defined.


Lemma pre_IE_impl_right : (Γ ⊢ A) + {
      forall l0 A0 l1, l0 ++ [A0] ++ l1 = Γ -> Q_impl_right A l0 A0 l1}.
Proof.
  specialize (list_split_ind  formula (Γ ⊢ A)  (Q_impl_right A) Γ f_impl_right) as [Fine | NotFine].
  - left. assumption.
  - right.
    intros l0 A0 l1 H.
    apply NotFine.
    assumption.
Defined.


Lemma provable_with_IE_impl_right :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_impl_right _ => False
        | _ => True
        end
  }.
Proof.
  specialize pre_IE_impl_right as [Done | Workie].
  -  left. assumption.
  - right.
    s_struct.
    destruct p; trivial.
    unfold Q_impl_right in Workie.
    specialize (Workie Γ0 (A0 ⇒ B) (Γ' ++ [A0] ++ Γ'')).
    assert (Γ0 ++ [A0 ⇒ B] ++ Γ' ++ [A0] ++ Γ'' = Γ).
    {
      auto.
    }
    apply (Workie H Γ' Γ'' A0 B); try reflexivity.
    auto.
Defined.





End ElimRules.


