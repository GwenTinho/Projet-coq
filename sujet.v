(* Projet du cours Preuves assistées par ordinateur 2024 :

   Prouveur automatique et certifié pour la logique intuitioniste
   propositionnelle.

   Ce projet a pour but de formaliser en Coq le calcul LI introduit
   par Jörg Hudelmaier, notamment dans l’article suivant (et
   précédemment dans sa thèse) :

   Jörg Hudelmaier, An O(n log n)-Space Decision Procedure for
   Intuitionistic Propositional Logic, 1993.

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

Require Import String.

Definition var := string.

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

Require Import List.

Import ListNotations.

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

Require Import ZArith Psatz.

(* On prouvera que toute formule a un degré supérieur ou égal à 2. *)
Lemma deg_at_least_two : forall A, deg A >= 2.
Proof.
  intro A.
  induction A;
    simpl; lia.
Qed.
  

(* On prouvera des propriétés sur les degrés des conjonctions et
   disjonctions. *)
Lemma deg_and_sum : forall A B, deg A + deg B < deg (A ∧ B).
Proof.
  intros A B.
  induction A; try (simpl;
    induction B;
                    simpl; lia).
  + simpl in IHA1, IHA2.
    simpl. lia.
  + simpl in IHA1, IHA2.
    simpl. lia.
  + simpl. simpl in IHA1, IHA2.
    Search (?k + ?n < ?k  + ?m).
    apply Arith_prebase.lt_n_S_stt.
    Search (?a + ?b = ?b + ?a).
    rewrite Nat.add_comm.
    apply Nat.add_lt_mono_l.
    Search (?a * ?m < ?a * ?n).
    Search ((?n * ?m) * ?p = ?n * (?m * ?p)).
    rewrite Arith_prebase.mult_assoc_reverse_stt.
    apply Mult.mult_lt_compat_l_stt.
    * Search (?a < ?a + ?b ).
      Search (?a < ?b -> ?b < ?c -> ?a < ?c).
      apply Nat.lt_trans with (deg A2 + deg B).
  - apply Nat.lt_add_pos_r.
    destruct B; lia.
  - lia.
    * lia.
Qed.

Lemma deg_or_intro_left : forall A B, deg A < deg (A ∨ B).
Proof.
  intros A B.
  induction A; simpl; lia.
Qed.

Lemma deg_or_intro_right : forall A B, deg B < deg (A ∨ B).
Proof.
  intros A B.
  induction A; simpl; lia.
Qed.

Lemma deg_IE_bot : forall Γ, deg_sequent (Γ ⊢? ⊥) >= deg_sequent ([] ⊢? ⊥).
Proof.
  intros Γ.
  simpl. lia.
Qed.


Lemma deg_II_or_left : forall Γ A B, deg_sequent (Γ ⊢? A) < deg_sequent (Γ ⊢? A ∨ B).
Proof.
  intros Γ A B.
  specialize (deg_at_least_two A).
  specialize (deg_at_least_two B).
  intros H H0.
  induction Γ.
  - simpl. lia.
  - unfold deg_sequent, deg_context in *. simpl in *.
    lia.
Qed.


Lemma deg_II_or_right : forall Γ A B, deg_sequent (Γ ⊢? B) < deg_sequent (Γ ⊢? A ∨ B).
Proof.
  intros Γ A B.
  specialize (deg_at_least_two A).
  specialize (deg_at_least_two B).
  intros H H0.
  induction Γ.
  - simpl. lia.
  - unfold deg_sequent, deg_context in *. simpl in *.
    lia.
Qed.


(* On prouvera que les prémisses des règles ont des degrés plus petits
   que les conclusions. *)
Lemma deg_IE_and :
  forall  Γ0 A B Γ1 C,
  deg_sequent (Γ0 ++ [A; B] ++ Γ1 ⊢? C) < deg_sequent (Γ0 ++ [A ∧ B] ++ Γ1 ⊢? C).
Proof.
  intros Γ0 A B  Γ1 C.
  induction Γ0.
  - simpl.
    induction  Γ1.
    + simpl.
      apply Nat.add_lt_mono_r.
      specialize (deg_and_sum A B) as G.
      simpl in G.
      unfold deg_context.
      simpl.
      lia.
    + apply Nat.add_lt_mono_r.
      unfold deg_context.
      simpl.
      specialize (deg_and_sum A B) as G.
      simpl in G.
      lia.
  - simpl.
    simpl in IHΓ0.
    unfold deg_context.
    simpl.
    unfold deg_context in IHΓ0.
    simpl in IHΓ0.
    lia.
Qed.

Lemma deg_II_and_left :  forall  Γ A B,
    deg_sequent (Γ  ⊢? A) < deg_sequent (Γ ⊢? A ∧ B).
Proof.
  intros Γ A B.
  induction Γ.
  - simpl. specialize (deg_at_least_two B). specialize (deg_at_least_two A). nia.
  - unfold deg_sequent, deg_context in *. simpl in *.
    specialize (deg_at_least_two A).
    specialize (deg_at_least_two B).
    specialize (deg_at_least_two a).
    nia.
Qed.

Lemma deg_II_and_right :   forall  Γ A B,
    deg_sequent (Γ  ⊢? B) < deg_sequent (Γ ⊢? A ∧ B).
Proof.
  intros Γ A B.
  induction Γ.
  - simpl. specialize (deg_at_least_two B). specialize (deg_at_least_two A). nia.
  - unfold deg_sequent, deg_context in *. simpl in *.
    specialize (deg_at_least_two A).
    specialize (deg_at_least_two B).
    specialize (deg_at_least_two a).
    nia.
Qed.


Lemma deg_IE_or_left :
  forall Γ0 A B Γ1 C,
  deg_sequent (Γ0 ++ [A] ++ Γ1 ⊢? C) < deg_sequent (Γ0 ++ [A ∨ B] ++ Γ1 ⊢? C).
Proof.
  intros Γ0 A B Γ1 C.
  induction  Γ0.
  + simpl.
    unfold deg_context.
    simpl.
    specialize (deg_or_intro_left A B) as H.
    simpl in H.
    lia.
  + specialize (deg_or_intro_left A B) as H. simpl in H.
    unfold deg_sequent, deg_context.
    unfold deg_sequent, deg_context in IHΓ0.
    simpl.
    simpl in IHΓ0.
    lia.
Qed.
    
Lemma deg_IE_or_right :
  forall Γ0 A B Γ1 C,
  deg_sequent (Γ0 ++ [B] ++ Γ1 ⊢? C) < deg_sequent (Γ0 ++ [A ∨ B] ++ Γ1 ⊢? C).
Proof.
  intros Γ0 A B Γ1 C.
  induction  Γ0.
  + simpl.
    unfold deg_context.
    simpl.
    specialize (deg_or_intro_left A B) as H.
    simpl in H.
    lia.
  + specialize (deg_or_intro_left A B) as H. simpl in H.
    unfold deg_sequent, deg_context.
    unfold deg_sequent, deg_context in IHΓ0.
    simpl.
    simpl in IHΓ0.
    lia.
Qed.

Lemma deg_II_impl :
  forall Γ A B,
  deg_sequent (Γ ++ [A] ⊢? B) < deg_sequent (Γ ⊢? A ⇒ B).
Proof.
  intros Γ A B.
  induction Γ.
  + simpl. unfold deg_context. simpl.
    specialize (deg_at_least_two A) as HA.
    specialize (deg_at_least_two B) as HB.
    induction (deg A); lia.
  + specialize (deg_at_least_two A) as HA.
    specialize (deg_at_least_two B) as HB.
    unfold deg_sequent,deg_context in IHΓ.
    simpl in IHΓ.
    unfold deg_sequent, deg_context.
    simpl.
    lia.
Qed.
    
Lemma deg_context_app : forall Γ1 Γ2, deg_context (Γ1 ++ Γ2) = deg_context Γ1 + deg_context Γ2.
Proof.
  intros Γ1 Γ2.
  unfold deg_context.
  rewrite map_app.
  rewrite list_sum_app.
  reflexivity.
Qed.

Lemma deg_sequent_app : forall Γ1 Γ2 A, deg_sequent (Γ1 ++ Γ2 ⊢? A ) = deg_context Γ1 + deg_context Γ2 + deg A.
Proof.
  intros Γ1 Γ2 A.
  simpl.
  rewrite deg_context_app.
  reflexivity.
Qed.

Lemma deg_context_element : forall A, deg_context [A] = deg A.
Proof.
  intro A.
  unfold deg_context.
  simpl.
  lia.
Qed.

Lemma deg_context_cons : forall A B, deg_context [A;B] = deg A + deg B.
Proof.
  intros A B.
  unfold deg_context.
  simpl.
  lia.
Qed.

Lemma deg_IE_impl_left :
  forall Γ A Γ' B Γ'' C,
  deg_sequent (Γ ++ [A] ++ Γ' ++ [B] ++ Γ'' ⊢? C) <
    deg_sequent (Γ ++ [A] ++ Γ' ++ [A ⇒ B] ++ Γ'' ⊢? C).
Proof.
  intros Γ A Γ' B Γ'' C.
  induction Γ'.
  + simpl.
    specialize (deg_II_impl Γ A B) as H.
    induction Γ''.
  -
    repeat rewrite deg_sequent_app.
    simpl.
    repeat rewrite deg_sequent_app in H.
    simpl in H.
    repeat rewrite deg_context_app.
    repeat rewrite deg_context_cons.
    simpl.
    lia.
  - repeat rewrite deg_sequent_app in *.
    repeat rewrite deg_context_app in *.
    simpl in *.
    unfold deg_context in *. simpl in *.
    lia.
    + repeat rewrite deg_sequent_app in *.
      repeat rewrite deg_context_app in *.
      unfold deg_context in *. simpl in *. lia.
Qed.

Lemma deg_IE_impl_right :
  forall Γ A Γ' B Γ'' C,
  deg_sequent (Γ ++ [B] ++ Γ' ++ [A] ++ Γ'' ⊢? C) <
    deg_sequent (Γ ++ [A ⇒ B] ++ Γ' ++ [A] ++ Γ'' ⊢? C).
Proof.
    intros Γ A Γ' B Γ'' C.
  induction Γ'.
  + simpl.
    specialize (deg_II_impl Γ A B) as H.
    induction Γ''.
  -
    repeat rewrite deg_sequent_app.
    simpl.
    repeat rewrite deg_sequent_app in H.
    simpl in H.
    repeat rewrite deg_context_app.
    repeat rewrite deg_context_cons.
    simpl.
    lia.
  - repeat rewrite deg_sequent_app in *.
    repeat rewrite deg_context_app in *.
    simpl in *.
    unfold deg_context in *. simpl in *.
    lia.
    + repeat rewrite deg_sequent_app in *.
      repeat rewrite deg_context_app in *.
      unfold deg_context in *. simpl in *. lia.
Qed.

Lemma deg_IE_impl_top :
  forall Γ A Γ' B,
  deg_sequent (Γ ++ [A] ++ Γ' ⊢? B) <
    deg_sequent (Γ ++ [⊤ ⇒ A] ++ Γ' ⊢? B).
Proof.
  intros Γ A Γ' B.
  induction Γ'.
  + repeat rewrite deg_sequent_app.
    unfold deg_context. simpl.
    lia.
  + repeat rewrite deg_sequent_app in *.
    unfold deg_context in *. simpl in *.
    lia.
Qed.

Lemma deg_IE_impl_and :
  forall Γ A B C Γ' D,
  deg_sequent (Γ ++ [A ⇒ B ⇒ C] ++ Γ' ⊢? D) <
    deg_sequent (Γ ++ [A ∧ B ⇒ C] ++ Γ' ⊢? D).
Proof.
  intros Γ A B C Γ' D.
  induction Γ'.
  + 
    repeat rewrite deg_sequent_app.
    unfold deg_context.
    simpl.
    Search ((?a * ?b) * ?c).
    apply Plus.plus_lt_compat_r_stt.
    apply Plus.plus_lt_compat_l_stt.
    specialize (deg_at_least_two A) as HA.
    Search (S ?a < S ?b).
    apply Arith_prebase.lt_n_S_stt.
    Search (?a + 0).
    repeat rewrite Nat.add_0_r.
    rewrite <- Nat.mul_assoc.
    Search (?a * ?b < ?a * ?c).
    apply Mult.mult_lt_compat_l_stt.
    * simpl.
      induction C; simpl; try lia.
    * lia.
  + repeat rewrite deg_sequent_app in *.
    unfold deg_context in *.
    simpl in *.
    lia.
Qed.
    
      
Lemma deg_IE_impl_or :
  forall Γ A B C Γ' D,
  deg_sequent (Γ ++ [A ⇒ C] ++ [B ⇒ C] ++ Γ' ⊢? D) <
    deg_sequent (Γ ++ [A ∨ B ⇒ C] ++ Γ' ⊢? D).
Proof.
  intros Γ A B C Γ' D.
  induction Γ.
  - simpl.
    apply Arith_prebase.lt_n_S_stt.
    Search (_ + ?n < _ + ?n).
    repeat apply add_lt_mono_r_proj_l2r.
    Search (S _ + _).
    rewrite <- plus_Sn_m.
    Search (((?a + ?b) + ?c)).
    rewrite Nat.add_assoc.
    repeat apply add_lt_mono_r_proj_l2r.
    specialize (deg_at_least_two A) as HA.
    specialize (deg_at_least_two B) as HB.
    specialize (deg_at_least_two C) as HC.
    lia.
  - repeat rewrite deg_sequent_app in *.
    repeat rewrite deg_context_app in *.
    simpl in *.
    lia.
Qed.

Check deg.

  

Lemma deg_IE_impl_impl_left :
  forall Γ A B C Γ' D,
  deg_sequent (Γ ++ [A; B ⇒ C] ++ Γ' ⊢? B) <
    deg_sequent (Γ ++ [(A ⇒ B) ⇒ C] ++ Γ' ⊢? D).
Proof.
  
  intros Γ A B C Γ' D.
    specialize (deg_at_least_two A) as HA.
    specialize (deg_at_least_two B) as HB.
    specialize (deg_at_least_two C) as HC.
    specialize (deg_at_least_two D) as HD.
    repeat rewrite deg_sequent_app.
    repeat rewrite deg_context_app.
    repeat rewrite <- Nat.add_assoc.
    apply add_lt_mono_l_proj_l2r.
    rewrite Nat.add_comm.
    Check Nat.add_comm.
    rewrite Nat.add_comm with (n := deg_context [(A ⇒ B) ⇒ C]).
    repeat rewrite <- Nat.add_assoc.
    apply add_lt_mono_l_proj_l2r.
    unfold deg_context. simpl.
    nia.
Qed.

Lemma deg_IE_impl_impl_right :
  forall Γ A B C Γ' D,
  deg_sequent (Γ ++ [C] ++ Γ' ⊢? D) <
    deg_sequent (Γ ++ [(A ⇒ B) ⇒ C] ++ Γ' ⊢? D).
Proof.
  
  intros Γ A B C Γ' D.
    specialize (deg_at_least_two A) as HA.
    specialize (deg_at_least_two B) as HB.
    specialize (deg_at_least_two C) as HC.
    specialize (deg_at_least_two D) as HD.
    repeat rewrite deg_sequent_app.
    repeat rewrite deg_context_app.
    repeat rewrite <- Nat.add_assoc.
    apply add_lt_mono_l_proj_l2r.
    rewrite Nat.add_comm.
    Check Nat.add_comm.
    rewrite Nat.add_comm with (n := deg_context [(A ⇒ B) ⇒ C]).
    repeat rewrite <- Nat.add_assoc.
    apply add_lt_mono_l_proj_l2r.
    unfold deg_context. simpl.
    nia.
Qed.

(* On pourra avoir envie de définir le lemme suivant, qui est le
   pendant dans Set du lemme in_split de la bibliothèque standard :

   Lemma in_split: forall [A : Type] (x : A) (l : list A), In x l ->
     exists l1 l2 : list A, l = l1 ++ x :: l2.

   Quand on cherchera une formule A dans un contexte Γ, on voudra
   construire un séquent avec Γ1 ++ [A] ++ Γ2, et on aura besoin pour
   cela que Γ1 et Γ2 puisse être extraits d’un type sigma, plutôt que
   cacher dans une existentielle.
 *)

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

(*
Je me rappelle plus exactement comment j'ai fait dans les détails mais je me souviens que c'était important que le Q soit quantifié dans la récurrence parce qu'on utilise un Q différent pour l'hyp d'induction
Mon début d'induction ressemble à ça
intros A P Q l.
  (Il est important d'avoir "∀Q" dans l'hypothèse de récurrence, 
    car dans la valeur retournée par f, les args de Q dépendent 
    de la taille de l)
  generalize Q. clear Q.
  induction l as [|hd tl ih]
 *)
(*
Lemma list_split_aux {A P Q} :
        forall (l p : list A)
        (f : forall l0 x l1, l0 ++ [x] ++ l1 = p ++ l -> P + { Q l0 x l1 })
        (fp : forall l0 x l1 l2, l0 ++ [x] ++ l1 = p ++ l ->
            l0 ++ [x] ++ l2 = p -> Q l0 x l1),
          P + { forall l0 x l1, l0 ++ [x] ++ l1 = p ++ l -> Q l0 x l1 }.
Proof.
  intros l p f fp.
  *)


    

  (*Idea assert into existence a function that lets us get the prefix
    We need aux taking the list and the accumulator, forall l forall acc
   *)

  (*
  assert (Prefix : forall post acc : list A, acc ++ post = l  -> P + { forall l0 x l1, l0 ++ [x] ++ l1 = l -> Q (acc ++ l0) x l1 }).
  induction l.
  - intros post acc eq.
    right.
    intros l0 x l1 H.
    Search (_ ++ _ = []).
    apply app_eq_nil in H.
    destruct H.
    inversion H0.
  - intros post acc eq.
    specialize (IHl post (tl acc)) as IHl0.
    cut (acc ++ post = a :: l -> tl acc ++ post = l).
    + intro eq0.
      apply eq0 in eq as eq1.
      apply IHl0 in eq1 as IHl1.
      destruct IHl1.
      * left. assumption.
      * right.
        intros l0 x l1 eq2.
        admit.
    + intros.
    
Admitted.
*)
(*Defined*)  
(* On prouve la décidabilité de LI par induction sur les
   dérivations. Pour pouvoir découper la preuve en lemmes intermédiaires
   tout en ayant accès à l’hypothèse d’induction, on introduit une
   section où l’on fait cette hypothèse. À l’issue de cette section,
   nous terminons la preuve en appliquant les lemmes par induction. *)

Lemma list_factor_empty : forall {A}  (l0 l1 : list A) (a : A), l0 ++ a :: l1 <> [].
Proof.
  intros A l0 l1 a Neg.
  induction l0; inversion Neg.
Qed.

Ltac kill_empty := match goal with
                       | H : (?l0 ++ ?a :: ?l1 = []) |-  _  => (apply list_factor_empty in H; contradiction)
                   end.


 Lemma increasing_sequent_degree : forall B Γ A, deg_sequent (Γ ⊢? A) < deg_sequent ((B :: Γ) ⊢? A).
  Proof.
    intro B.
    simpl.
    unfold deg_context.
    simpl.
    specialize (deg_at_least_two B).
    lia.
  Qed.


  Lemma list_split_in : forall A P Q l (eq_dec : forall a b: A, {a = b} + {a <> b} ) (f : forall x : A, In x l -> P + {Q x}), P + {forall x, In x l -> Q x}.
  Proof.
    intros A P Q l eq_dec f.
    generalize dependent  Q.
    induction l.
    - intros Q f.
      right.
      intros x H.
      inversion H.
    - intros Q f.
      simpl in *.
      assert (g := f).
      specialize (f a) as [Easy | Annoying].
      +  left. reflexivity.
      + left. assumption.
      + right.
        intros x [Eq | Right].
        * rewrite <- Eq. assumption.
        * assert (Q0 := Q).
          admit.
        (*  assert (h := fun x (p : In x l) => if eq_dec x a then Annoying else g x (or_intror p)).*)
       
Admitted.


 



 Lemma list_split_ind:
  forall A P Q (l : list A)
  (f : forall l0 x l1, l0 ++ [x] ++ l1 = l -> P + { Q l0 x l1 }),
  P + { forall l0 x l1, l0 ++ [x] ++ l1 = l -> Q l0 x l1 }.
Proof. (* Defined plutôt que Qed *)
  intros A P Q l.
  
  assert (Prefix : forall post acc : list A, acc ++ post = l  -> P + { forall l0 x l1, l0 ++ [x] ++ l1 = l -> Q (acc ++ l0) x l1 }).
  generalize dependent Q.
  induction l.
  - intros Q post acc H.
    right.
    intros l0 x l1 H0.
    simpl in H0.
      kill_empty.
  - intros Q post acc H.
    (*Idea: if i find the element within l -> ok, if i dont check if a is the element*)
    admit.
Admitted.

Lemma zero_context_is_empty : forall Γ, deg_context Γ = 0 -> Γ = [].
Proof.
  intros Γ H.
  induction Γ.
  - reflexivity.
  - unfold deg_context in H. simpl in H. specialize (deg_at_least_two a). lia.
Qed.
  

 (*IDEA: implement lemmas from the paper itself*)

  (*notably: most rules of LG are invertible*)

Example from_text :  forall A C D E F, [(A ∨ (D ∧ (E ⇒  (C ∨ D)))) ⇒ D] ⊢ (A ⇒ (D ∧ (E ⇒ (C ∨ D)))) ∨ F.
Proof.
  intros A C D E F.
  apply II_or_left.
  apply II_impl.
  specialize (@IE_impl_or [] [A]) as H.
  apply H.
  simpl.
  clear H.
  apply II_and.
  - apply @IE_impl_and with (Γ := [A ⇒ D]) (Γ' := [A]).
    apply @IE_impl_right with (Γ := []).
    apply @IE_impl_left with (Γ := []) (Γ' := []).
    simpl.
    apply @I_ax with (Γ := []) (Γ' := [(E ⇒ C ∨ D) ⇒ D; A]).
  - apply II_impl.
    apply II_or_right.
    apply @IE_impl_and with (Γ := [A ⇒ D]) (Γ' := [A;E]).
    apply @IE_impl_right with (Γ := []) (Γ'' := [E]).
    simpl.
    apply @IE_impl_left with (Γ := []) (Γ' := []) (Γ'' := [A;E] ).
    simpl.
    apply @I_ax with (Γ := []).
Qed.

Lemma deg_context_geq_O : forall Γ, deg_context Γ >= 0.
Proof.
  unfold deg_context.
  induction Γ.
  - lia.
  - specialize (deg_at_least_two a).
    intro H. simpl. lia.
Qed.

Lemma deg_sequent_geq_two : forall Γ A, deg_sequent (Γ ⊢? A) >= 2.
Proof.
  intros Γ A.
  simpl.
  specialize (deg_context_geq_O Γ).
  specialize (deg_at_least_two A).
  intros H H0.
  lia.
Qed.
  

Lemma var_characteristic : forall Γ x,  (Γ ⊢ Var x) -> In (Var x) Γ.
Proof.
  intros Γ x.
  
  induction Γ.
  - intro H. inversion H; kill_empty.
  - intro H.
    destruct (formula_eq_dec a (Var x)) as [L | R].
    + simpl. left. assumption.
    + simpl. right.

Admitted.
    

    
    
    

  
Section LI_Decidable.
  Variable S : sequent.

  Let Γ : list formula := let '(Γ ⊢? A) := S in Γ.

  Let A : formula := let '(Γ ⊢? A) := S in A.

  Variable IH : forall Γ' A',
      deg_sequent (Γ' ⊢? A') < deg_sequent (Γ ⊢? A) -> (Γ' ⊢ A') + { notT (Γ' ⊢ A') }.

  (* Cette section a pour but de prouver le (gros) lemme suivant.
     Ne pas hésiter à écrire des lemmes intermédiaires auparavant
     pour vérifier l’applicabilité de chaque règle. *)

  Lemma is_provable_rec_top : let A := ⊤ in Γ ⊢ ⊤.
  Proof.
    apply II_top.
  Defined.

  Lemma is_provable_rec_bot :  A = ⊥ -> notT (Γ ⊢ ⊥).
  Proof.
    intros AisBot Provable.
    induction Γ.
    - inversion Provable;
        (
          apply list_factor_empty in H0 +
                                    apply list_factor_empty in H);
        contradiction.
    - specialize (IH l).
      specialize (increasing_sequent_degree a) as Inc.
      rewrite AisBot in *.
      apply IH in Inc.
      destruct Inc as [L | R].
      + apply IHl.
        * intros.
          admit.
        * assumption.
      + admit.
  Admitted.
                 
  
  Lemma is_provable_rec :
    (Γ ⊢ A) + { notT (Γ ⊢ A) }.
  Proof.
    remember (deg_sequent (Γ ⊢? A)) as n.
    induction n.
    - specialize (deg_sequent_geq_two Γ A) as Absurd. lia.
    - induction A.
      + left. apply II_top.
      + specialize (deg_IE_bot Γ) as Geq.
        rewrite <- Heqn in Geq.
        specialize (Nat.eq_dec (Datatypes.S n) (deg_sequent ([] ⊢? ⊥))) as [L | R].
        * simpl in L. rewrite Heqn in L. simpl in L.
          cut (deg_context Γ = 0).
          -- intro H.
             apply zero_context_is_empty in H.
             rewrite H in *.
             clear H L.
             right.
             intro K.
             inversion K; kill_empty.
          -- lia.
        * Search (?a <= ?b /\ ?a <> ?b).
          cut (deg_sequent ([] ⊢? ⊥) <= Datatypes.S n /\  deg_sequent ([] ⊢? ⊥) <> Datatypes.S n).
          -- intro Hyp.
             specialize (proj2 (Nat.le_neq (deg_sequent ([] ⊢? ⊥)) (Datatypes.S n)) Hyp) as K.
             assert (J : deg_sequent ([] ⊢? ⊥) < Datatypes.S n). assumption.
             apply IH in K.
             destruct K as [LL | RR].
             ++  inversion LL; kill_empty.
             ++ simpl in J.
                left.
                induction Γ.
                ** rewrite Heqn in J.
                  simpl in J.
                  lia.
                ** admit.
          -- admit.
      + admit.
      + specialize (deg_II_and_left Γ f1 f2) as F1.
        specialize (deg_II_and_right Γ f1 f2) as F2.
        rewrite <- Heqn in F1,F2.
        apply IH in F1,F2.
        destruct F1 as [F1 | NF1];
          destruct F2 as [F2| NF2].
        * left. apply II_and; assumption.
        * right.
          intro K.    
          inversion K.
          -- admit.
          -- apply NF2.
             rewrite <- H0.
             apply IE_bot.
          -- contradiction.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
        * admit.
        * admit.
      + specialize (deg_II_or_left Γ f1 f2) as F1.
        specialize (deg_II_or_right Γ f1 f2) as F2.
        rewrite <- Heqn in F1,F2.
        apply IH in F1,F2.
        destruct F1 as [F1 | NF1]; destruct F2 as [F2 | NF2].
        * left. apply II_or_left. assumption.
        * left. apply II_or_left. assumption.
        * left. apply II_or_right. assumption.
        * right. intro K.
          inversion K.
          -- specialize (Nat.eq_dec (Datatypes.S n) (deg_sequent (Γ ⊢? f1))) as [L | R].
             ++ apply IHf1 in L.
                ** admit.
                ** admit.
             ++ admit.
          -- apply NF1.
             rewrite <- H0.
             apply IE_bot.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
      + specialize (deg_II_impl Γ f1 f2) as F.
        rewrite <- Heqn in F.
        apply IH in F.
        destruct F as [F | NF].
        * left. apply II_impl. assumption.
        * admit.
Admitted.

             
           
        
          
        
        
      
  (*Notes:
    Implment a decision algorithm:
    Prove for a fragment of the logic.
    Go to def of LI and comment out parts of the logic
    Send thierry.martinez@inria.fr loads of mails
    Make proof as modular as possible
    Prove rule by rule
    For each rule can we kow how to prove it given a rule
    Express a that we cannot find a proof by continuing with the present rule
    Refutation is hard
    We dont want to introduce codependence between rules
    Filter out the proofs
    For each already proven thing
    if match p with II and  _ _ _ _ => False, else True
    Simplifies refuation!

   *)
   (* Defined. *)
End LI_Decidable.

(* On peut facilement déduire is_provable de is_provable_rec par
   induction. Noter que le type du prouveur garantie sa correction et
   sa complétude vis-à-vis de LI ! *)
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

(* On se donne quelques variables. *)
Definition A := Var "A"%string.

Definition B := Var "B"%string.

Definition C := Var "C"%string.

(* Et on teste le prouveur sur les propositions du TD 1. *)
Lemma A_imp_A : is_provable_bool ([] ⊢? A ⇒ A) = true.
Proof.
Admitted.

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
