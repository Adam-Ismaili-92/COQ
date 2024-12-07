(* Exercice 1 *)

(* Q1 *)

Proposition modus_ponens :
  forall A B : Prop, (A -> B) -> A -> B.
Proof.
  intros.
  apply H.
  assumption.
Qed.

(* Q2 *)

Proposition implication_transitivity :
  forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.

(* Q3 *)

Proposition modus_tollens :
  forall A B : Prop, (A -> B) -> ~B -> ~A.
Proof.
  intros.
  intro.
  apply H0.
  apply H.
  assumption.
Qed.

(* Exercice 2 *)

(* Q1 *)

Proposition question_1 :
  forall A B : Prop, ((A \/ B) -> False) -> (A -> False).
Proof.
  intros.
  apply H.
  left.
  assumption.
Qed.

(* Q2 *)

Proposition question_2 :
  forall A B : Prop, ((A \/ B) -> False) -> (B -> False).
Proof.
  intros.
  apply H.
  right.
  assumption.
Qed.

(* Exercice 3 *)

(* Q1 *)

Proposition de_morgan_bool_1 :
  forall a b:bool, negb(orb a b) = andb (negb a) (negb b).
Proof.
  intros.
  destruct a.
  - destruct b.
    -- simpl.
      reflexivity.
    -- simpl.
      reflexivity.
  - destruct b.
    -- simpl.
    reflexivity.
    -- simpl.
      reflexivity.
Qed.

(* Q2 *)

Proposition de_morgan_bool_2 :
  forall a b:bool, (orb (negb a) (negb b)) = negb (andb a b).
Proof.
  intros.
  destruct a.
  - destruct b.
    -- simpl.
      reflexivity.
    -- simpl.
      reflexivity.
  - destruct b.
    -- simpl.
    reflexivity.
    -- simpl.
      reflexivity.
Qed.

(* Exercice 4 *)

(* Q1 *)

Proposition de_morgan_1 :
  forall P Q, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  split.
  - intro.
    apply H.
    left.
    assumption. 
  - intro.
    apply H.
    right.
    assumption.
Qed.

(* Q2 *)

Proposition de_morgan_2 :
  forall P Q, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros.
  intro.
  destruct H.
  destruct H0.
  - apply H.
    assumption.
  - apply H1.
    assumption.
Qed.

(* Q3 *)

Proposition de_morgan_1_2 :
  forall P Q, ~P /\ ~Q <-> ~(P \/ Q).
Proof.
  intros.
  split.
  - apply de_morgan_2.
  - apply de_morgan_1.
Qed.

(* Q4 *)

Proposition de_morgan_inv_1 :
  forall P Q, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros.
  intro.
  destruct H.
  destruct H0.
  - apply H.
    assumption.
  - apply H.
    apply H0.
Qed.

Proposition de_morgan_inv_2 :
  forall P Q, ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  (* tkt *)
Admitted.


Proposition de_morgan_classic:
  forall P Q, ~P \/ ~Q <-> ~(P /\ Q).
Proof.
  intros.
  split.
  - apply de_morgan_inv_1.
  - apply de_morgan_inv_2.
Qed.

(* Exercice 5 *)

(* Q1 *)

Proposition excluded_middle_irrefutable :
  forall P:Prop, ~~(P \/ ~P).
Proof.
  intros.
  intro.
  apply H.
  right.
  intro.
  apply H.
  left.
  assumption.
Qed.

(* Q2 *)


Proposition double_neg_implies_excluded :
  (forall P: Prop, ~~P -> P) -> (forall P, (P \/ ~P)).
Proof.
  intros.
  apply H.
  intro.
  apply H0.
  right.
  intro.
  apply H0.
  left.
  assumption.
Qed.

(* Q3 *)

Proposition excluded_implies_demorgan:
  (forall P : Prop, P \/ ~P) -> (forall P Q : Prop, ~(P /\ Q) -> ~P \/ ~Q).
Proof.
  (* Tkt *)
Admitted.
