From LIDec Require Import base.
From LIDec Require Import listSplitting.
From LIDec Require Import misc.
Require Import List.

Import ListNotations.

Section IntroRules.

Variable S : sequent.

Let Γ : list formula := let '(Γ ⊢? A) := S in Γ.

Let A : formula := let '(Γ ⊢? A) := S in A.

Variable IH : forall Γ' A',
    deg_sequent (Γ' ⊢? A') < deg_sequent (Γ ⊢? A) -> (Γ' ⊢ A') + { notT (Γ' ⊢ A') }.

Lemma provable_with_II_top :
  (Γ ⊢ A) +
  { forall (p: LI S),
    match p return Prop with II_top => False | _ => True end }.
Proof.
  destruct (formula_eq_dec A ⊤) as [A_eq_top | A_neq_top].
  - left. rewrite A_eq_top. apply II_top.
  - right. intro p.
    assert (let '(Γ ⊢? A) := S in A <> ⊤) as fst_S_neq_top. {
      destruct S. assumption.
    }
    destruct p; trivial.
    auto.
Defined.



Lemma provable_with_I_ax :
   (Γ ⊢ A) +
  { forall (p: LI S),
      match p return Prop with I_ax => False | _ => True  end }.
Proof.
  destruct (in_dec_formula A Γ) as [A_in | A_nin].
  - left.
    apply in_split_formula in A_in.
    destruct A_in as [[pre post] eq].
    simpl in eq.
    rewrite eq.
    apply I_ax.
  - right. intro p.
    assert (let '(Γ ⊢? A) := S in ~ In A Γ) as A_nin_ctx_S. {
      destruct S. assumption.
    }
    destruct p; trivial.
    apply A_nin_ctx_S.
    apply in_or_app.
    right.
    apply in_or_app.
    left.
    simpl.
    auto.
Defined.


Lemma provable_with_II_and :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | II_and _ _ => False
        | _ => True
        end
  }.
Proof.
   assert (S = (Γ ⊢? A)) as S_struct. {
    destruct S.
    reflexivity.
   }
   induction A.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - destruct (formula_eq_dec A (f1 ∧ f2)) as [EQ | NEQ].
     +
       specialize (IH Γ f1) as F1.
       specialize (IH Γ f2) as F2.
       specialize (deg_II_and_left Γ f1 f2) as L.
       specialize (deg_II_and_right Γ f1 f2) as R.
       apply F1 in L.
       apply F2 in R.
       clear F1 F2.
       destruct L as [T | F];destruct R as [T0 | F0].
       * left. apply II_and; assumption.
       * right. intro p. assert (let '(Γ ⊢? A) := S in notT (A =  f2)) as A_neq_f2.
         {
           destruct S. intro N. inversion S_struct. rewrite N in H0. symmetry in H0. apply weird_left in H0. easy.
         }
         destruct S. destruct p; trivial.
         inversion S_struct.
         subst.
         contradiction.
       * right. intro p. assert (let '(Γ ⊢? A) := S in notT (A = f1)) as A_neq_f1.
         {
           destruct S. intro N. inversion S_struct. rewrite N in H0. symmetry in H0. apply weird_right in H0. easy.
         }
         destruct S. destruct p; trivial.
         inversion S_struct.
         subst.
         contradiction.
       * right. intro p. assert (let '(Γ ⊢? A) := S in notT (A = f1 /\ A = f2)) as A_neq_f1_and_f2.
         {
           destruct S. intros [N1 N2]. inversion S_struct.
           subst.
           symmetry in H0.
           apply weird_left in H0.
           easy.
         }
         destruct S. destruct p; trivial.
         inversion S_struct.
         subst.
         contradiction.
     + right.
       intro p.
       assert (let '(Γ ⊢? A) := S in notT (A = f1 ∧  f2)) as A_neq_f1_f2.
       {
         destruct S. intro N. auto.
       }
       destruct p; trivial.
       inversion S_struct.
       subst.
       auto.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
Defined.



Lemma provable_with_II_or_left :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | II_or_left _ => False
        | _ => True
        end
  }.
Proof.
   assert (S = (Γ ⊢? A)) as S_struct. {
    destruct S.
    reflexivity.
   }
   induction A.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - destruct (formula_eq_dec A (f1 ∨ f2)) as [EQ | NEQ].
     + specialize (deg_II_or_left Γ f1 f2) as F1.
       specialize (deg_II_or_right Γ f1 f2) as F2.
       apply IH in F1, F2.
       destruct F1 as [F1 | NF1]; destruct F2 as [F2 | NF2].
       * left. apply II_or_left. assumption.
       * left. apply II_or_left. assumption.
       * left. apply II_or_right. assumption.
       * right.
         intro p.
         assert (let '(Γ ⊢? A) := S in notT (A = f1 /\ A =  f2)) as A_neq_f1_f2.
         {
           destruct S. intros [L R]. inversion S_struct. rewrite L in H0. symmetry in H0. apply weird_or_right in H0. easy.
         }
         destruct S.
         destruct p; trivial.
         inversion S_struct.
         subst.
         auto.
     + right.
       intro p.
       assert (let '(Γ ⊢? A) := S in notT (A = f1 ∨  f2)) as A_neq_f1_or_f2.
       {
         destruct S. auto.
       }
       destruct p; trivial.
       inversion S_struct.
       subst.
       auto.
   -  right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
Defined.


Lemma provable_with_II_or_right :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | II_or_right _ => False
        | _ => True
        end
  }.
Proof.
   assert (S = (Γ ⊢? A)) as S_struct. {
    destruct S.
    reflexivity.
   }
   induction A.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - destruct (formula_eq_dec A (f1 ∨ f2)) as [EQ | NEQ].
     + specialize (deg_II_or_left Γ f1 f2) as F1.
       specialize (deg_II_or_right Γ f1 f2) as F2.
       apply IH in F1, F2.
       destruct F1 as [F1 | NF1]; destruct F2 as [F2 | NF2].
       * left. apply II_or_left. assumption.
       * left. apply II_or_left. assumption.
       * left. apply II_or_right. assumption.
       * right.
         intro p.
         assert (let '(Γ ⊢? A) := S in notT (A = f1 /\ A =  f2)) as A_neq_f1_f2.
         {
           destruct S. intros [L R]. inversion S_struct. rewrite L in H0. symmetry in H0. apply weird_or_right in H0. easy.
         }
         destruct S.
         destruct p; trivial.
         inversion S_struct.
         subst.
         auto.
     + right.
       intro p.
       assert (let '(Γ ⊢? A) := S in notT (A = f1 ∨  f2)) as A_neq_f1_or_f2.
       {
         destruct S. auto.
       }
       destruct p; trivial.
       inversion S_struct.
       subst.
       auto.
   -  right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
Defined.


Lemma provable_with_II_impl :
   (Γ ⊢ A) +
  { forall (p : LI S),
        match p with
        | II_impl _ => False
        | _ => True
        end
  }.
Proof.
   assert (S = (Γ ⊢? A)) as S_struct. {
    destruct S.
    reflexivity.
   }
   induction A.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - right. intro p. destruct S. inversion S_struct. destruct p; trivial. inversion S_struct.
   - destruct (formula_eq_dec A (f1 ⇒ f2)) as [EQ | NEQ].
     + specialize (deg_II_impl Γ f1 f2) as F.
       apply IH in F.
       destruct F as [F | NF].
       * left. apply II_impl. assumption.
       * right.
         intro p.
         assert (let '(Γ ⊢? A) := S in notT (Γ ++ [f1] ⊢ f2)) as A_neq_f1_impl_f2.
         {
           destruct S. assumption.
         }
         destruct S.
         destruct p; trivial.
         inversion S_struct.
         subst.
         auto.
     + right.
       intro p.
       assert (let '(Γ ⊢? A) := S in notT (A = f1 ⇒  f2)) as A_neq_f1_or_f2.
       {
         destruct S. auto.
       }
       destruct p; trivial.
       inversion S_struct.
       subst.
       auto.
Defined.

End IntroRules.
