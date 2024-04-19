From LIDec Require Import base.
Require Import List.

Import ListNotations.
Require Import ZArith Psatz.

Lemma in_split_specif :
  forall {A} (eq_dec : forall x y : A, {x = y}+{x <> y}) {x : A} {l : list A},
    In x l ->
    { p : list A * list A | l = fst p ++ x :: snd p }.
Proof.
  intros A eq_dec x l K.
  induction l.
  - inversion K.
  - simpl in K.
    specialize (eq_dec a x) as eq_a_x.
    destruct eq_a_x.
    + exists ([],l).
      simpl.
      rewrite e.
      reflexivity.

    + cut (forall A B,( ~A) -> (A \/ B) -> B).
      intro H.
      specialize (H (a = x) (In x l)).
      specialize (H n K).
      * apply IHl in H.
        destruct H as (p,e).
        exists (a :: fst p, snd p).
        simpl.
        rewrite e.
        reflexivity.
      * intros A0 B M [L|R].
        -- contradiction.
        -- assumption.
Defined.
Check in_split_specif.
Definition in_split_formula {x l} := @in_split_specif formula formula_eq_dec x l.
Definition in_dec_formula := in_dec formula_eq_dec.
(* Important : la preuve devra être terminée par Defined
plutôt que Qed pour que la définition de ce lemme soit transparente de
sorte qu’on puisse réduire ce lemme lors des calculs. *)


(* On pourra plus généralement avoir envie de définir le lemme
   suivant, qui sait chercher une preuve (P) mettant en jeu un élément
   distingué dans une liste (en particulier, une formule dans un
   contexte), ou conclure (Q) qu’il n’en existe pas. *)
Lemma tl_is_empty : forall A (l : list A), tl l = [] -> (exists x, l = [x]) \/ l = [].
Proof.
  intros A l.
  induction l.
  - intro H.
    right. reflexivity.
  - intro H.
    left.
    exists a.
    f_equal.
    simpl in H.
    assumption.
Qed.

Lemma list_factor_empty : forall {A}  (l0 l1 : list A) (a : A), l0 ++ a :: l1 <> [].
Proof.
  intros A l0 l1 a Neg.
  induction l0; inversion Neg.
Qed.

Ltac kill_empty := match goal with
                       | H : (?l0 ++ ?a :: ?l1 = []) |-  _  => (apply list_factor_empty in H; contradiction)
                   end.

  Lemma list_empty_dec : forall {A} (l : list A), {l = []} + {l <> []}.
  Proof.
    intros A l.
    induction l.
    - left. reflexivity.
    - destruct IHl as [Empty | NEmpty].
      + right.
        rewrite Empty.
        intro N.
        inversion N.
      + right.
        intro N. inversion N.
   Defined.

Lemma In_fi_split_dec : forall {A}(eq_dec : forall x y : A, {x = y}+{x <> y}) {x : A} {l : list A},
    {'(l0, l1) | l = l0 ++ [x] ++ l1} -> In x l.
Proof.
  intros A eq_dec x l [[pre post] eq].
  rewrite eq.
  apply in_or_app.
  right.
  apply in_or_app.
  left.
  simpl.
  auto.
Qed.

Lemma in_exists : forall {A} (l : list A), l <> [] -> {'(x) | In x l}.
Proof.
  intros A l H.
  induction l.
  - contradiction.
  - exists a. simpl. auto.
Qed.


Lemma split_dec : forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A),
    {'(l0,x, l1) | l = l0 ++ [x] ++ l1} + {l = []}.
Proof.
  intros A eq_dec l.
  specialize (list_empty_dec l) as [E | NE].
  - right. assumption.
  - left.
    apply in_exists in NE.
    destruct NE as [x p].
    apply (in_split_specif eq_dec) in p.
    destruct p as [[a b] eq].
    simpl in eq.
    exists (a,x,b).
    auto.
Qed.



 Lemma list_split_ind:
  forall A P Q (l : list A) (f : forall l0 x l1, l0 ++ [x] ++ l1 = l -> P + { Q l0 x l1 }),
  P + { forall l0 x l1, l0 ++ [x] ++ l1 = l -> Q l0 x l1 }.
 Proof. (* Defined plutôt que Qed *)
   intros A P Q l f.
   assert (K : forall (post acc : list A), acc ++ post = l -> P + { forall l0 x
                                                              l1, l0 ++ [x] ++ l1 = post -> Q (acc ++ l0) x l1 }).
   {
     intros post.
     induction post.
     - intros acc H.
       right.
       intros l0 x l1 H0.
       simpl in H0.
       kill_empty.
     - intros acc H.
       specialize (f acc a post) as [Ok | Bad].
       + simpl. assumption.
       + left. assumption.
       + specialize (IHpost (acc ++ [a])).
         assert ((acc ++ [a]) ++ post = l).
         {
           rewrite <- app_assoc.
           simpl.
           assumption.
         }
         apply IHpost in H0.
         destruct H0 as [Ok0 | Bad0].
         * left. assumption.
         * right.
           intros l0 x l1 H0.
           destruct l0.
           -- simpl in H0.
              inversion H0.
              rewrite app_nil_r.
              assumption.
           -- specialize (Bad0 l0 x l1).
              simpl in H0.
              inversion H0.
              subst.
              assert (acc ++ a :: l0 = (acc ++ [a]) ++ l0).
              {
                rewrite <- app_assoc.
                reflexivity.
              }
              rewrite H.
              apply Bad0.
              reflexivity.
   }
   apply (K l []).
   reflexivity.
Defined.
   
(*
  intros A P Q l.

  generalize dependent Q.
  induction l.
  - intros Q post acc H.
    right.
    intros l0 x l1 H0.
    simpl in H0.
      kill_empty.
  - intros Q post acc H.
    specialize (list_empty_dec acc) as [Acc_nil | Acc_not_nil].
    + specialize (IHl Q (tl post) []).
    assert ( tl post = l).
    {
      rewrite Acc_nil in H. simpl in H. rewrite H. reflexivity.
    }
    simpl in IHl.
    apply IHl in H0.
    destruct H0 as [L | R].
      * left. assumption.
      * right. intros l0 x l1 H0.
        apply R.
        rewrite Acc_nil.
        simpl.
        admit.
     + admit.
  -  admit.
Admitted.

*)


Lemma zero_context_is_empty : forall Γ, deg_context Γ = 0 -> Γ = [].
Proof.
  intros Γ H.
  induction Γ.
  - reflexivity.
  - unfold deg_context in H. simpl in H. specialize (deg_at_least_two a). lia.
Qed.


Definition context_eq_dec := list_eq_dec formula_eq_dec.



Lemma decidable_context_split : forall (A : formula) Γ, Γ <> []   -> {'(Γ',Γ'') | Γ' ++ [A] ++ Γ'' = Γ} + {forall Γ' Γ'', Γ <> Γ' ++ [A] ++ Γ''}.
Proof.
  intros A Γ H.
  - specialize (in_dec_formula A Γ) as [Ok | Bad].
    + apply in_split_formula in Ok.
      destruct Ok as [(L,R) eq].
      simpl in eq.
      left.
    exists (L,R).
    auto.
  + right.
    intros Γ' Γ'' N.
    apply Bad.
    rewrite N.
    apply in_or_app.
    right.
    simpl.
    auto.
Qed.

Lemma context_split_ex : forall Γ : list formula, Γ <> [] ->  {'(Γ',Γ'', A) | Γ' ++ [A] ++ Γ'' = Γ}.
Proof.
  intros Γ H.
  induction Γ.
  - easy.
  - specialize (list_empty_dec Γ) as [Nil | NNil].
    + exists ([], [], a). rewrite Nil. reflexivity.
    + apply IHΓ in NNil.
      destruct NNil as [t eq].
      destruct t as [[l r] A].
      exists (a::l,r, A). rewrite <- eq. reflexivity.
Defined.


Lemma decidable_start_of_context : forall (A : formula) Γ, Γ <> [] -> { 'Δ | Γ = A :: Δ } +  { forall Δ, notT (Γ = A :: Δ) } .
Proof.
  intros A Γ H.
  destruct Γ.
  - contradiction.
  - specialize (formula_eq_dec A f) as [Eq | Neq].
    + left. exists Γ. subst. easy.
    + right. intros Δ N. inversion N. auto.
Qed.
