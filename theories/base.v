(*   Intuitionistic Propositional Logic, 1993.

   Il s’agit d’un calcul des séquents pour la logique intuitioniste
   qui vérifie la propriété qu'on ne peut pas construire de dérivation
   infinie : on peut en effet définir une notion de degré sur les
   séquents, qui décroit strictement à chaque étape de la
   dérivation. Nous démontrerons en Coq cette propriété, qui garantie
   la terminaison du prouveur. *)

(* Nous pourrons utiliser les chaînes de caractères pour représenter
   les variables.  Dans la démonstration, nous utilisons seulement le
   fait que l’égalité entre deux variables est décidable, pour en
   dériver la décidabilité de l’égalité entre formules. Dans les tests
   proposés à la fin, nous aurons besoin de trois variables distinctes
   A, B et C. Toute la démonstration devrait fonctionner à l’identique
   si on remplace le type string par un type énuméré A, B ou C... *)

Require Import ZArith Psatz.
Require Import List.

Import ListNotations.

Definition var := nat.

(* Le type des formules, avec les notations associées pour plus de
   lisibilité. *)

Inductive formula :=
| Top
| Bottom
| Var (x : var)
| And (A B : formula)
| Or (A B : formula)
| Imply (A B : formula).

Scheme Equality for formula.

Infix "∧" := And (at level 10).

Infix "∨" := Or (at level 20).

Infix "⇒" := Imply (at level 30, right associativity).

Notation "⊤" := Top.

Notation "⊥" := Bottom.

(* Nous utilisons les listes pour représenter la partie gauche des
   séquents. *)



(* Un séquent intuitioniste a une liste de formules dans sa partie
   gauche et une seule formule dans sa partie droite. *)

Inductive sequent : Set :=
  Sequent (Γ : list formula) (A : formula).

(* Nous notons les segments Γ ⊢? A, par contraste avec Γ ⊢ A qui
   désigne un segment prouvable. *)

Infix "⊢?" := Sequent (at level 90).

Reserved Infix "⊢" (at level 70).

(* Le calcul LI, présenté sous la forme d’un inductif avec un
   constructeur par règle d’inférence. *)

Inductive LI : sequent -> Set :=
| I_ax : forall {Γ Γ' A},
    Γ ++ [A] ++ Γ' ⊢ A
| II_top : forall {Γ},
    (* Note : ⊤ n’était pas pris en compte dans la présentation de
       Hudelmaier, il n’y avait donc ni règle II_top, ni règle
       IE_impl_top. *)
    Γ ⊢ ⊤
| IE_bot : forall {Γ Γ' A},
    Γ ++ [⊥] ++ Γ' ⊢ A
| II_and : forall {Γ A B},
    Γ ⊢ A -> Γ ⊢ B ->
    Γ ⊢ A ∧ B
| IE_and : forall {Γ Γ' A B C},
    Γ ++ [A; B] ++ Γ' ⊢ C ->
    Γ ++ [A ∧ B] ++ Γ' ⊢ C
| II_or_left : forall {Γ A B},
    Γ ⊢ A ->
    Γ ⊢ A ∨ B
| II_or_right : forall {Γ A B},
    Γ ⊢ B ->
    Γ ⊢ A ∨ B
| IE_or : forall {Γ Γ' A B C},
    Γ ++ [A] ++ Γ' ⊢ C -> Γ ++ [B] ++ Γ' ⊢ C ->
    Γ ++ [A ∨ B] ++ Γ' ⊢ C
| II_impl : forall {Γ A B},
    Γ ++ [A] ⊢ B ->
    Γ ⊢ A ⇒ B
(* Les règles d’éliminitation de l’implication sont découpées de façon
   à garantir la terminaison des dérivations. *)
| IE_impl_left : forall {Γ Γ' Γ'' A B C},
    Γ ++ [A] ++ Γ' ++ [B] ++ Γ'' ⊢ C ->
    Γ ++ [A] ++ Γ' ++ [A ⇒ B] ++ Γ'' ⊢ C
| IE_impl_right : forall {Γ Γ' Γ'' A B C},
    Γ ++ [B] ++ Γ' ++ [A] ++ Γ'' ⊢ C ->
    Γ ++ [A ⇒ B] ++ Γ' ++ [A] ++ Γ'' ⊢ C
| IE_impl_top : forall {Γ Γ' A B},
    Γ ++ [A] ++ Γ' ⊢ B ->
    Γ ++ [⊤ ⇒ A] ++ Γ' ⊢ B
| IE_impl_and : forall {Γ Γ' A B C D},
    Γ ++ [A ⇒ B ⇒ C] ++ Γ' ⊢ D ->
    Γ ++ [A ∧ B ⇒ C] ++ Γ' ⊢ D
| IE_impl_or : forall {Γ Γ' A B C D},
    Γ ++ [A ⇒ C] ++ [B ⇒ C] ++ Γ' ⊢ D ->
    Γ ++ [A ∨ B ⇒ C] ++ Γ' ⊢ D
| IE_impl_impl : forall {Γ Γ' A B C D},
    Γ ++ [A; B ⇒ C] ++ Γ' ⊢ B -> Γ ++ [C] ++ Γ' ⊢ D ->
    Γ ++ [(A ⇒ B) ⇒ C] ++ Γ' ⊢ D
where "G ⊢ A" := (LI (G ⊢? A)).

Hint Constructors LI : core.

(* On peut montrer la terminaison en définissant une notion de degré
   pour les formules, puis pour les séquents : on montre ensuite que
   le degré décroit strictement entre la conclusion des règles et
   leurs prémisses. *)

Fixpoint deg (f : formula) : nat :=
  match f with
  | ⊤ | ⊥ | Var _ => 2
  | A ∧ B => deg A * (1 + deg B)
  | A ∨ B => 1 + deg A + deg B
  | A ⇒ B => 1 + deg A * deg B
  end.

(* Le degré d’un contexte est la somme des degrés des formules qui y
   apparaissent. *)
Definition deg_context (l : list formula) : nat :=
  list_sum (map deg l).

(* Idem pour un séquent. *)
Definition deg_sequent '(Γ ⊢? A) : nat :=
  deg_context Γ + deg A.

Hint Unfold deg_context : core.
Hint Unfold deg_sequent : core.



(* On prouvera que toute formule a un degré supérieur ou égal à 2. *)
Lemma deg_at_least_two : forall A, deg A >= 2.
Proof.
  intro A. induction A; simpl; lia.
Defined.

Ltac deg_two var name := specialize (deg_at_least_two var) as name.

(* On prouvera des propriétés sur les degrés des conjonctions et
   disjonctions. *)
Lemma deg_and_sum : forall A B, deg A + deg B < deg (A ∧ B).
Proof.
  intros A B.
  deg_two A H.
  deg_two B H0.
  simpl. nia.
Defined.

Lemma deg_or_intro_left : forall A B, deg A < deg (A ∨ B).
Proof.
  intros A B.
  deg_two A H.
  deg_two B H0.
  simpl. lia.
Defined.

Lemma deg_or_intro_right : forall A B, deg B < deg (A ∨ B).
Proof.
  intros A B.
  deg_two A H.
  deg_two B H0.
  simpl. lia.
Defined.

Lemma deg_IE_bot : forall Γ, deg_sequent (Γ ⊢? ⊥) >= deg_sequent ([] ⊢? ⊥).
Proof.
  intros Γ.
  simpl. lia.
Defined.


Lemma deg_context_geq_O : forall Γ, deg_context Γ >= 0.
Proof.
  unfold deg_context.
  induction Γ.
  - lia.
  - specialize (deg_at_least_two a).
    intro H. simpl. lia.
Defined.

Lemma deg_sequent_geq_two : forall Γ A, deg_sequent (Γ ⊢? A) >= 2.
Proof.
  intros Γ A.
  simpl.
  specialize (deg_context_geq_O Γ).
  specialize (deg_at_least_two A).
  intros H H0.
  lia.
Defined.


Lemma deg_context_app : forall Γ1 Γ2, deg_context (Γ1 ++ Γ2) = deg_context Γ1 + deg_context Γ2.
Proof.
  intros Γ1 Γ2.
  unfold deg_context.
  rewrite map_app.
  rewrite list_sum_app.
  reflexivity.
Defined.

Lemma deg_sequent_app : forall Γ1 Γ2 A, deg_sequent (Γ1 ++ Γ2 ⊢? A ) = deg_context Γ1 + deg_context Γ2 + deg A.
Proof.
  intros Γ1 Γ2 A.
  simpl.
  rewrite deg_context_app.
  reflexivity.
Defined.

Lemma deg_context_element : forall A, deg_context [A] = deg A.
Proof.
  intro A.
  unfold deg_context.
  simpl.
  lia.
Defined.

Lemma deg_context_cons : forall A B, deg_context [A;B] = deg A + deg B.
Proof.
  intros A B.
  unfold deg_context.
  simpl.
  lia.
Defined.


Lemma deg_II_or_left : forall Γ A B, deg_sequent (Γ ⊢? A) < deg_sequent (Γ ⊢? A ∨ B).
Proof.
  intros Γ A B.
  deg_two A H.
  deg_two B H0.
  specialize (deg_context_geq_O Γ) as H1.
  simpl.
  lia.
Defined.


Lemma deg_II_or_right : forall Γ A B, deg_sequent (Γ ⊢? B) < deg_sequent (Γ ⊢? A ∨ B).
Proof.
  intros Γ A B.
  deg_two A H.
  deg_two B H0.
  specialize (deg_context_geq_O Γ) as H1.
  simpl.
  lia.
Defined.


(* On prouvera que les prémisses des règles ont des degrés plus petits
   que les conclusions. *)
Lemma deg_IE_and :
  forall  Γ0 A B Γ1 C,
  deg_sequent (Γ0 ++ [A; B] ++ Γ1 ⊢? C) < deg_sequent (Γ0 ++ [A ∧ B] ++ Γ1 ⊢? C).
Proof.
  intros Γ0 A B  Γ1 C.
  deg_two A H.
  deg_two B H0.
  deg_two C H1.
  specialize (deg_context_geq_O
                Γ0) as H2.
  specialize (deg_context_geq_O Γ1) as H3.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  unfold deg_context.
  simpl.
  nia.
Defined.

Lemma deg_II_and_left :  forall  Γ A B,
    deg_sequent (Γ  ⊢? A) < deg_sequent (Γ ⊢? A ∧ B).
Proof.
  
  intros Γ A B.
  deg_two A H.
  deg_two B H0.
  specialize (deg_context_geq_O
                Γ) as H1.
  simpl. nia.
Defined.

Lemma deg_II_and_right :   forall  Γ A B,
    deg_sequent (Γ  ⊢? B) < deg_sequent (Γ ⊢? A ∧ B).
Proof.
  
  intros Γ A B.
  deg_two A H.
  deg_two B H0.
  specialize (deg_context_geq_O
                Γ) as H1.
  simpl. nia.
Defined.


Lemma deg_IE_or_left :
  forall Γ0 A B Γ1 C,
  deg_sequent (Γ0 ++ [A] ++ Γ1 ⊢? C) < deg_sequent (Γ0 ++ [A ∨ B] ++ Γ1 ⊢? C).
Proof.
  intros Γ0 A B  Γ1 C.
  deg_two A H.
  deg_two B H0.
  deg_two C H1.
  specialize (deg_context_geq_O
                Γ0) as H2.
  specialize (deg_context_geq_O Γ1) as H3.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  unfold deg_context.
  simpl.
  nia.
Defined.

Lemma deg_IE_or_right :
  forall Γ0 A B Γ1 C,
  deg_sequent (Γ0 ++ [B] ++ Γ1 ⊢? C) < deg_sequent (Γ0 ++ [A ∨ B] ++ Γ1 ⊢? C).
Proof.
  intros Γ0 A B  Γ1 C.
  deg_two A H.
  deg_two B H0.
  deg_two C H1.
  specialize (deg_context_geq_O
                Γ0) as H2.
  specialize (deg_context_geq_O Γ1) as H3.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  unfold deg_context.
  simpl.
  nia.
Defined.

Lemma deg_II_impl :
  forall Γ A B,
  deg_sequent (Γ ++ [A] ⊢? B) < deg_sequent (Γ ⊢? A ⇒ B).
Proof.
  
  intros Γ A B.
  deg_two A H.
  deg_two B H0.
  specialize (deg_context_geq_O
                Γ) as H1.
  rewrite deg_sequent_app.
  rewrite deg_context_element.
  simpl.
  nia.
Defined.

Lemma deg_IE_impl_left :
  forall Γ A Γ' B Γ'' C,
  deg_sequent (Γ ++ [A] ++ Γ' ++ [B] ++ Γ'' ⊢? C) <
    deg_sequent (Γ ++ [A] ++ Γ' ++ [A ⇒ B] ++ Γ'' ⊢? C).
Proof.
  intros Γ A Γ' B Γ'' C.
  deg_two A H.
  deg_two B H0.
  deg_two C H1.
  specialize (deg_context_geq_O
                Γ) as H2.
  specialize (deg_context_geq_O Γ') as H3.
  specialize (deg_context_geq_O Γ'') as H4.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  repeat rewrite deg_context_element.
  simpl.
  nia.
Defined.

Lemma deg_IE_impl_right :
  forall Γ A Γ' B Γ'' C,
  deg_sequent (Γ ++ [B] ++ Γ' ++ [A] ++ Γ'' ⊢? C) <
    deg_sequent (Γ ++ [A ⇒ B] ++ Γ' ++ [A] ++ Γ'' ⊢? C).
Proof.
  intros Γ A Γ' B Γ'' C.
  deg_two A H.
  deg_two B H0.
  deg_two C H1.
  specialize (deg_context_geq_O
                Γ) as H2.
  specialize (deg_context_geq_O Γ') as H3.
  specialize (deg_context_geq_O Γ'') as H4.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  repeat rewrite deg_context_element.
  simpl.
  nia.
Defined.

Lemma deg_IE_impl_top :
  forall Γ A Γ' B,
  deg_sequent (Γ ++ [A] ++ Γ' ⊢? B) <
    deg_sequent (Γ ++ [⊤ ⇒ A] ++ Γ' ⊢? B).
Proof.
  intros Γ A Γ' B.
  deg_two A H.
  deg_two B H0.
  specialize (deg_context_geq_O
                Γ) as H1.
  
  specialize (deg_context_geq_O
                Γ') as H2.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  simpl.
  rewrite deg_context_element.
  nia.
Defined.

Lemma deg_IE_impl_and :
  forall Γ A B C Γ' D,
  deg_sequent (Γ ++ [A ⇒ B ⇒ C] ++ Γ' ⊢? D) <
    deg_sequent (Γ ++ [A ∧ B ⇒ C] ++ Γ' ⊢? D).
Proof.
  intros Γ A B C Γ' D.
  deg_two A H.
  deg_two B H0.
  deg_two C H1.
  deg_two D H2.
  specialize (deg_context_geq_O
                Γ) as H3.
  
  specialize (deg_context_geq_O
                Γ') as H4.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  simpl.
  nia.
Defined.


Lemma deg_IE_impl_or :
  forall Γ A B C Γ' D,
  deg_sequent (Γ ++ [A ⇒ C] ++ [B ⇒ C] ++ Γ' ⊢? D) <
    deg_sequent (Γ ++ [A ∨ B ⇒ C] ++ Γ' ⊢? D).
Proof.
  
  intros Γ A B C Γ' D.
  deg_two A H.
  deg_two B H0.
  deg_two C H1.
  deg_two D H2.
  specialize (deg_context_geq_O
                Γ) as H3.
  
  specialize (deg_context_geq_O
                Γ') as H4.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  simpl.
  nia.
Defined.



Lemma deg_IE_impl_impl_left :
  forall Γ A B C Γ' D,
  deg_sequent (Γ ++ [A; B ⇒ C] ++ Γ' ⊢? B) <
    deg_sequent (Γ ++ [(A ⇒ B) ⇒ C] ++ Γ' ⊢? D).
Proof.
  
  intros Γ A B C Γ' D.
  deg_two A H.
  deg_two B H0.
  deg_two C H1.
  deg_two D H2.
  specialize (deg_context_geq_O
                Γ) as H3.
  
  specialize (deg_context_geq_O
                Γ') as H4.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  rewrite deg_context_cons.
  repeat rewrite deg_context_element.
  simpl.
  nia.
Defined.

Lemma deg_IE_impl_impl_right :
  forall Γ A B C Γ' D,
  deg_sequent (Γ ++ [C] ++ Γ' ⊢? D) <
    deg_sequent (Γ ++ [(A ⇒ B) ⇒ C] ++ Γ' ⊢? D).
Proof.
  intros Γ A B C Γ' D.
  deg_two A H.
  deg_two B H0.
  deg_two C H1.
  deg_two D H2.
  specialize (deg_context_geq_O
                Γ) as H3.
  
  specialize (deg_context_geq_O
                Γ') as H4.
  unfold deg_sequent.
  repeat rewrite deg_context_app.
  repeat rewrite deg_context_element.
  simpl.
  nia.
Defined.

 Lemma increasing_sequent_degree : forall B Γ A, deg_sequent (Γ ⊢? A) < deg_sequent ((B :: Γ) ⊢? A).
  Proof.
    intro B.
    simpl.
    unfold deg_context.
    simpl.
    specialize (deg_at_least_two B).
    lia.
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

Lemma decidable_or : forall A0, { '(B, C) | A0 = B ∨ C } + { forall B C, A0 <> B ∨ C }.
Proof.
  intro A0.
  induction A0.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
  - left. exists (A0_1,A0_2). reflexivity.
  - right. intros B C N. inversion N.
Defined.


Lemma decidable_impl_and : forall A0, { '(B, C, D) | A0 = (B ∧ C) ⇒ D } + { forall B C D, A0 <> (B ∧ C) ⇒ D }.
Proof.
  intro A0.
  induction A0.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - destruct (decidable_and A0_1) as [[[B C] eq] | BAD].
    + left. exists (B, C, A0_2). rewrite eq. reflexivity.
    + right. intros B C D. intro N. inversion N. apply (BAD B C). assumption.
Defined.

Lemma decidable_impl_or : forall A0, { '(B, C, D) | A0 = (B ∨ C) ⇒ D } + { forall B C D, A0 <> (B ∨ C) ⇒ D }.
Proof.
  intro A0.
  induction A0.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - destruct (decidable_or A0_1) as [[[B C] eq] | BAD].
    + left. exists (B, C, A0_2). rewrite eq. reflexivity.
    + right. intros B C D. intro N. inversion N. apply (BAD B C). assumption.
Defined.

Lemma decidable_impl : forall A0, { '(B, C) | A0 = (B ⇒ C) } + { forall B C, A0 <> (B ⇒ C) }.
Proof.
  intro A0.
  induction A0.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
  - right. intros B C N. inversion N.
  - left. exists (A0_1, A0_2). reflexivity.
Defined.

Lemma decidable_impl_top : forall A0, { '(B) | A0 = (⊤ ⇒ B) } + { forall B, A0 <> (⊤ ⇒ B) }.
Proof.
  intro A0.
  induction A0.
  - right. intros B N. inversion N.
  - right. intros B N. inversion N.
  - right. intros B N. inversion N.
  - right. intros B N. inversion N.
  - right. intros B N. inversion N.
  -specialize (formula_eq_dec A0_1 ⊤) as [eq | neq].
    + left. exists A0_2. congruence.
    + right. intros B N. inversion N. contradiction.
Defined.



Lemma decidable_impl_impl : forall A0, { '(B, C, D) | A0 = (B ⇒ C) ⇒ D } + { forall B C D, A0 <> (B ⇒ C) ⇒ D }.
Proof.
  intro A0.
  induction A0.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - right. intros B C D N. inversion N.
  - destruct (decidable_impl A0_1) as [[[B C] eq] | BAD].
    + left. exists (B, C, A0_2). rewrite eq. reflexivity.
    + right. intros B C D. intro N. inversion N. apply (BAD B C). assumption.
Defined.
