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


Lemma decidable_and : forall A0, { '(B, C) | A0 = B ∧ C } + { forall B C, A0 <> B ∧ C }.
Proof.
  intro A0.
  induction A0.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
  - left. exists (A0_1,A0_2). reflexivity.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
Defined.

Definition Q_and (l : list formula) (A0 : formula) (r: list formula) := l ++ [A0] ++ r = Γ /\ (forall B C, A0  <> B ∧ C).
Definition P_and := {'(l,A0,r,B,C) | l ++ [A0] ++ r = Γ   /\  A0 = B ∧ C }.

Lemma either_P_and_or_Q_and : forall l A0 r, l ++ [A0] ++ r = Γ -> P_and + {Q_and l A0 r}.
Proof.
  intros l A0 r H.
  unfold P_and, Q_and.
  specialize (decidable_and A0) as [[[B C] eq] | Neq].
  - left. exists (l, A0, r, B, C). split; assumption.
  - right. split; assumption.
Defined.


Ltac dec A B L R:= specialize (formula_eq_dec A B) as [L |  R].

Lemma provable_with_IE_and :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_and _ => False
        | _ => True
        end
  }.
Proof.
  specialize (list_split_ind formula P_and Q_and Γ either_P_and_or_Q_and) as [P_holds | Every_Q_holds].
  - unfold P_and in P_holds.
    destruct P_holds as [[[[[l A0] r] B] C] [eq_Γ eq_A0]].
    subst.
    specialize (deg_IE_and l B C r A) as Deg.
    rewrite <- eq_Γ in IH.
    apply IH in Deg.
    destruct Deg as [Ok | Bad].
    + left.
      rewrite <- eq_Γ.
      apply IE_and.
      assumption.
    + right.
      intro p.
      assert (S = (Γ ⊢? A)) as S_struct.
      {
        destruct S. reflexivity.
      }
      destruct p; trivial.
      apply Bad.
      rewrite <- eq_Γ in S_struct.
      inversion S_struct.
      assert (Γ0 = l /\ Γ' = r).
      {
        split.
        * induction l.
      }
      
    


Admitted.


End ElimRules.


