From LIDec Require Import base.
From LIDec Require Import listSplitting.
From LIDec Require Import misc.
From LIDec Require Import introRules.
From LIDec Require Import elimRules.
From LIDec Require Import strongInduction.
Require Import List.

Import ListNotations.
Require Import ZArith Psatz.

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

  Ltac finish := left; destruct S; auto.
  
  Lemma is_provable_rec :
    (Γ ⊢ A) + { notT (Γ ⊢ A) }.
  Proof.
    specialize ( provable_with_I_ax S IH) as [G | B_I_Ax]. {finish. }
    specialize ( provable_with_II_top S IH) as [G | B_I_Top]. {finish. }
    specialize ( provable_with_II_and S IH) as [G | B_I_And]. {finish. }
    specialize ( provable_with_II_or_left S IH) as [G | B_I_Or_Left]. {finish. }    
    specialize ( provable_with_II_or_right S IH) as [G | B_I_Or_Right]. {finish. }
    specialize ( provable_with_II_impl S IH) as [G | B_I_Impl]. {finish. }
    specialize ( provable_with_IE_bot S IH) as [G | B_E_Bot]. {finish. }
    specialize ( provable_with_IE_and S IH) as [G | B_E_And]. {finish. }    
    specialize ( provable_with_IE_or S IH) as [G | B_E_Or]. {finish. }      
    specialize ( provable_with_IE_impl_top S IH) as [G | B_E_Impl_Top]. {finish. }
    specialize ( provable_with_IE_impl_left S IH) as [G | B_E_Impl_Left]. {finish. }
    specialize ( provable_with_IE_impl_right S IH) as [G | B_E_Impl_Right]. {finish. }
    specialize ( provable_with_IE_impl_and S IH) as [G | B_E_Impl_And]. {finish. }
    specialize ( provable_with_IE_impl_or S IH) as [G | B_E_Impl_Or]. {finish. }
    specialize ( provable_with_IE_impl_impl S IH) as [G | B_E_Impl_Impl]. {finish. }
    right.
    intro p.
    assert (S = (Γ ⊢? A)).
    { destruct S. auto. }
    rewrite <- H in p.
    specialize (B_I_Ax p).
    specialize (B_I_And p).
    specialize (B_I_Or_Left p).
    specialize (B_I_Or_Right p).
    specialize (B_I_Impl p).
    specialize (B_I_Top p).
    specialize (B_E_Impl_And p).
    specialize (B_E_Impl_Impl p).
    specialize (B_E_Impl_Or p).
    specialize (B_E_Impl_Right p).
    specialize (B_E_Impl_Left p).
    specialize (B_E_Impl_Top p).
    specialize (B_E_And p).
    specialize (B_E_Or p).
    specialize (B_E_Bot p).
    destruct p; assumption.
Defined.

End LI_Decidable.



Definition SI_Prop (n : nat) := forall Γ A, deg_sequent (Γ ⊢? A) = n -> (Γ ⊢ A) + { notT (Γ ⊢ A) }.

Lemma SI_IH : forall m : nat, (forall n0 : nat, n0 < m -> SI_Prop n0) -> SI_Prop m.
Proof.
  intros m H.
  unfold SI_Prop in *.
  intros Γ A H0.
  specialize (is_provable_rec (Γ ⊢? A)) as H1.
  simpl in *.
  apply H1.
  intros Γ' A' H2.
  rewrite H0 in H2.
  specialize (H (deg_sequent (Γ' ⊢? A')) H2 Γ' A').
  assert (deg_context Γ' + deg A' = deg_sequent (Γ' ⊢? A')).
  { reflexivity. }
  apply H in H3.
  assumption.
Defined.

Lemma is_provable :
  forall s,
  let '(Γ ⊢? A) := s in
  (Γ ⊢ A) + { notT (Γ ⊢ A) }.
Proof.
  intro s.
  induction s.
  remember (deg_sequent (Γ ⊢? A)) as n.
  generalize dependent Γ.
  generalize dependent A.
  specialize (strong_induction SI_Prop SI_IH) as IH.
  intros A Γ Heqn.
  apply IH with n.
  symmetry.
  assumption.
Defined.

(* Pour écrire plus facilement les tests, on oublie les preuves et on
   réduit la réponse du prouveur à un booléen. *)
Definition is_provable_bool '(Γ ⊢? A) : bool :=
  if is_provable (Γ ⊢? A) then
    true
  else
    false.
