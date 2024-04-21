From LIDec Require Import base.
From LIDec Require Import decider.
Require Import List.

Import ListNotations.

Require Import String.

(* On se donne quelques variables. *)
Definition A := Var "A"%string.

Definition B := Var "B"%string.

Definition C := Var "C"%string.

(* Et on teste le prouveur sur les propositions du TD 1. *)
Lemma A_imp_A : is_provable_bool ([] ⊢? A ⇒ A) = true.
Proof.
  reflexivity.
Qed.

Lemma imp_trans : is_provable_bool ([] ⊢? (A ⇒ B) ∧ (B ⇒ C) ⇒ (A ⇒ C)) = true.
Proof.
  reflexivity.
Qed.

Definition equiv A B := (A ⇒ B) ∧ (B ⇒ A).

Infix "⇔" := equiv (at level 30).

Lemma curry : is_provable_bool ([] ⊢? (A ∧ B ⇒ C) ⇔ (A ⇒ B ⇒ C)) = true.
Proof.
  reflexivity.
Qed.

Lemma and_assoc : is_provable_bool ([] ⊢? (A ∧ B) ∧ C ⇔ A ∧ (B ∧ C)) = true.
Proof.
  reflexivity.
Qed.

Lemma and_comm : is_provable_bool ([] ⊢? A ∧ B ⇔ B ∧ A) = true.
Proof.
  reflexivity.
Qed.

Lemma or_assoc : is_provable_bool ([] ⊢? (A ∨ B) ∨ C ⇔ A ∨ (B ∨ C)) = true.
Proof.
  reflexivity.
Qed.

Lemma or_comm : is_provable_bool ([] ⊢? A ∨ B ⇔ B ∨ A) = true.
Proof.
  reflexivity.
Qed.

Lemma and_top : is_provable_bool ([] ⊢? A ∧ ⊤ ⇔ A) = true.
Proof.
  reflexivity.
Qed.

Lemma and_bot : is_provable_bool ([] ⊢? A ∧ ⊥ ⇔ ⊥) = true.
Proof.
  reflexivity.
Qed.

Lemma or_top : is_provable_bool ([] ⊢? A ∨ ⊤ ⇔ ⊤) = true.
Proof.
  reflexivity.
Qed.

Lemma or_bot : is_provable_bool ([] ⊢? A ∨ ⊥ ⇔ A) = true.
Proof.
  reflexivity.
Qed.

Lemma and_dist_or : is_provable_bool ([] ⊢? A ∧ (B ∨ C) ⇔ A ∧ B ∨ A ∧ C) = true.
Proof.
  reflexivity.
Qed.

Lemma or_dist_and : is_provable_bool ([] ⊢? A ∨ (B ∧ C) ⇔ (A ∨ B) ∧ (A ∨ C)) = true.
Proof.
  reflexivity.
Qed.

Lemma imp_dist_and : is_provable_bool ([] ⊢? (A ⇒ (B ∧ C)) ⇔ (A ⇒ B) ∧ (A ⇒ C)) = true.
Proof.
  reflexivity.
Qed.

Lemma imp_dist_or : is_provable_bool ([] ⊢? ((A ∨ B) ⇒ C) ⇔ (A ⇒ C) ∧ (B ⇒ C)) = true.
Proof.
  reflexivity.
Qed.

Definition neg A := A ⇒ ⊥.

Notation "¬" := neg (at level 5).

Lemma neg_neg_not_provable : is_provable_bool ([] ⊢? ¬ (¬ A) ⇒ A) = false.
Proof.
  reflexivity.
Qed.

Lemma neg_neg : is_provable_bool ([] ⊢? A ⇒ ¬ (¬ A)) = true.
Proof.
  reflexivity.
Qed.

Lemma neg_neg_neg : is_provable_bool ([] ⊢? ¬ (¬ (¬ A)) ⇔ ¬ A) = true.
Proof.
  reflexivity.
Qed.

Lemma em_not_provable : is_provable_bool ([] ⊢? ¬ A ∨ A) = false.
Proof.
  reflexivity.
Qed.

Lemma neg_neg_em : is_provable_bool ([] ⊢? ¬ (¬ (¬ A ∨ A))) = true.
Proof.
  reflexivity.
Qed.

Lemma neg_top : is_provable_bool ([] ⊢? ¬ ⊤ ⇔ ⊥) = true.
Proof.
  reflexivity.
Qed.

Lemma neg_bot : is_provable_bool ([] ⊢? ¬ ⊥ ⇔ ⊤) = true.
Proof.
  reflexivity.
Qed.

Lemma neg_a_or_neg_b : is_provable_bool ([] ⊢? ¬ A ∨ ¬ B ⇒ ¬ (A ∧ B)) = true.
Proof.
  reflexivity.
Qed.

Lemma neg_a_and_b_not_provable : is_provable_bool ([] ⊢? ¬ (A ∧ B) ⇒ ¬ A ∨ ¬ B) = false.
Proof.
  reflexivity.
Qed.

Lemma neg_a_or_b : is_provable_bool ([] ⊢? ¬ (A ∨ B) ⇔ ¬ A ∧ (¬ B)) = true.
Proof.
  reflexivity.
Qed.

Lemma neg_neg_neg_a_and_b : is_provable_bool ([] ⊢? ¬ (¬ (¬ (A ∧ B) ⇔ ¬ A ∨ ¬ B))) = true.
Proof.
  reflexivity.
Qed.

Lemma imp_decomp_not_provable : is_provable_bool ([] ⊢? (A ⇒ B) ⇒ ¬ A ∨ B) = false.
Proof.
  reflexivity.
Qed.

Lemma imp_comp : is_provable_bool ([] ⊢? ¬ A ∨ B ⇒ (A ⇒ B)) = true.
Proof.
  reflexivity.
Qed.

Lemma neg_neg_imp_decomp : is_provable_bool ([] ⊢? ¬ (¬ ((A ⇒ B) ⇔ ¬ A ∨ B))) = true.
Proof.
  reflexivity.
Qed.

Lemma neg_imp_decomp_not_provable : is_provable_bool ([] ⊢? ¬ (A ⇒ B) ⇒ A ∧ (¬ B)) = false.
Proof.
  reflexivity.
Qed.

Lemma neg_imp_comp : is_provable_bool ([] ⊢? A ∧ (¬ B) ⇒ ¬ (A ⇒ B)) = true.
Proof.
  reflexivity.
Qed.

Lemma neg_neg_neg_imp_decomp : is_provable_bool ([] ⊢? ¬ (¬ (¬ (A ⇒ B) ⇔ A ∧ (¬ B)))) = true.
Proof.
  reflexivity.
Qed.

Lemma pierce_not_provable : is_provable_bool ([] ⊢? ((A ⇒ B) ⇒ A) ⇒ A) = false.
Proof.
  reflexivity.
Qed.

Lemma neg_neg_pierce : is_provable_bool ([] ⊢? ¬ (¬ (((A ⇒ B) ⇒ A) ⇒ A))) = true.
Proof.
  reflexivity.
Qed.
