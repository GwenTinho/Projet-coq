From LIDec Require Import base.
From LIDec Require Import listSplitting.
From LIDec Require Import misc.
From LIDec Require Import introRules.
Require Import List.

Import ListNotations.

(* On pourra avoir envie de définir le lemme suivant, qui est le
   pendant dans Set du lemme in_split de la bibliothèque standard :

   Lemma in_split: forall [A : Type] (x : A) (l : list A), In x l ->
     exists l1 l2 : list A, l = l1 ++ x :: l2.

   Quand on cherchera une formule A dans un contexte Γ, on voudra
   construire un séquent avec Γ1 ++ [A] ++ Γ2, et on aura besoin pour
   cela que Γ1 et Γ2 puisse être extraits d’un type sigma, plutôt que
   cacher dans une existentielle.
 *)



Section LI_Decidable.
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

Ltac dec A B L R:= specialize (formula_eq_dec A B) as [L |  R].

Ltac dec_list Γ Γ' L R := specialize (context_eq_dec Γ Γ') as [L | R].

Lemma provable_with_IE_and :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | IE_and _ => False
        | _ => True
        end
  }.
Proof.
  specialize (list_split_ind_dec formula ({'(h,x,k, B, C) | h ++ [x] ++ k = Γ /\ x = B ∧ C }) (fun a y b => forall B C, y <> B ∧ C) Γ formula_eq_dec) as H.
  


Admitted.





  Lemma is_provable_rec :
    (Γ ⊢ A) + { notT (Γ ⊢ A) }.
  Proof.


Admitted.

End LI_Decidable.

Lemma is_provable :
  forall s,
  let '(Γ ⊢? A) := s in
  (Γ ⊢ A) + { notT (Γ ⊢ A) }.
Proof.
Admitted.

(* Pour écrire plus facilement les tests, on oublie les preuves et on
   réduit la réponse du prouveur à un booléen. *)
Definition is_provable_bool '(Γ ⊢? A) : bool :=
  if is_provable (Γ ⊢? A) then
    true
  else
    false.
