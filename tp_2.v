(* TP 2 *)

(* Exercice 1 *)

(* Q1 *)

Require Import Arith.

Proposition plus_n_0 :
  forall n: nat, n + 0 = n.
Proof.
  intros.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Proposition other_plus_n_0 :
  forall n: nat, n + 0 = n.
Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

(* Q2 *)

Proposition double_is_plus:
  forall n : nat, n + n = 2 * n.
Proof.
  intros.
  simpl.
  rewrite other_plus_n_0.
  reflexivity.
Qed.

(* Q3 *)

Proposition add_succ_r :
  forall n m: nat, n + S m = S (n + m).
Proof.
  intros.
  induction n, m.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

(* Q4 *)

Proposition add_succ_l :
  forall n m: nat, S n + m = S (n + m).
Proof.
  intros.
  reflexivity.
Qed.

(* Exercice 2 *)

(* Q1 *)

Fixpoint even (n : nat) : Prop :=
  match n with
  | 0 => True
  | S 0 => False
  | S (S n') => even n'
  end.

(* Q2 *)

Proposition one_of_two_succ_is_even:
  forall n : nat, (even n) \/ (even (S n)).
Proof.
  intros.
  induction n.
  - simpl.
    left.
    reflexivity.
  - destruct IHn.
    -- right. 
       simpl. 
       assumption.
    -- left.  
       assumption.
Qed.

(* Q3 *)

Proposition but_not_both :
  forall n : nat, even n -> not (even (S n)).
Proof.
  intros.
  intro.
  induction n.
  - apply H0.
  - destruct IHn.
    -- apply H0.
    -- apply H.
Qed.

(* Q4 *)

Proposition double_is_even :
  forall n : nat, even (n * 2).
Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    assumption.
Qed.

(* Q5 *)

Proposition succ_double_is_odd :
  forall n : nat, ~(even (S (n * 2))).
Proof.
  intros.
  apply but_not_both.
  apply double_is_even.
Qed.

(* Exercice 3 *)

(* Q1 *)

Proposition pair_induction :
  forall (P : nat -> Prop),
  P 0 -> P 1 -> (forall n, P n -> P (S n) -> P (S (S n))) -> forall x, P x.
Proof.
  intros.
  assert (P x /\ P(S x)).
  induction x.
  - split ; assumption.
  - destruct IHx.
    split.
      -- assumption.
      -- apply H1 ; assumption.
  - apply H2.
Qed.

(* Q2 & Q3 *)

Proposition even_sum :
  forall (n m : nat), even n -> even m -> even (n + m).
Proof.
  intros.
  induction n using pair_induction.
  - simpl.
    assumption.
  - induction m using pair_induction.
    -- simpl.
       apply H.
    -- simpl.
       reflexivity.
    -- apply IHm.
       apply H0.
  - simpl.
    apply IHn.
    apply H.
Qed.