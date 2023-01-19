From Coq Require Import ArithRing.
From Coq Require Import Compare_dec.
From Coq Require Import Wf_nat.
From Coq Require Import Arith.
From Coq Require Import Lia.

Lemma add_zero_r : forall n, n + 0 = n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma x_times_2_is_even : forall x : nat,
  Nat.even (2*x) = true.
Proof.
  simpl.
  induction x.
  - simpl.
    reflexivity.
  - rewrite add_zero_r.
    rewrite add_zero_r in IHx.
    replace (S x + S x) with (S (S (x + x))).
    + simpl.
      apply IHx.
    + simpl.
      rewrite (Nat.add_comm x (S x)).
      simpl.
      reflexivity.
Qed.

Lemma even_exists : forall x : nat,
  Nat.even x = true -> exists k, 2*k = x.
Proof.
  intros.
  apply Nat.even_spec in H.
  unfold Nat.Even in H.
  destruct H.
  exists x0.
  symmetry.
  apply H.
Qed.

Lemma even_is_xor: forall x y : nat,
  Nat.even (x+y) = negb (xorb (Nat.even x) (Nat.even y)).
Proof.
Admitted.


Lemma square_even_is_even : forall x : nat,
  Nat.even (x*x) = Nat.even x.
Proof.
  intros.
  induction x.
  - simpl.
    reflexivity.
  - replace (S x * S x) with ((1 + x) * (1 + x)).
    2: {
      simpl.
      reflexivity.
    }
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_l.
    repeat rewrite Nat.mul_1_l.
    rewrite Nat.mul_add_distr_l.
    repeat rewrite Nat.mul_1_r.
    rewrite Nat.add_assoc.
    repeat rewrite <- Nat.add_assoc.
    repeat rewrite even_is_xor.
    repeat rewrite <- IHx.
    replace (Nat.even 1) with false.
    2 : { trivial. }
    rewrite -> Bool.xorb_false_l.
    rewrite -> Bool.xorb_nilpotent.
    rewrite -> Bool.negb_involutive.
    replace (negb false) with (true).
    2 : { trivial. }
    rewrite -> Bool.xorb_true_r.
    rewrite -> IHx.
    clear IHx.
    induction x.
    + simpl.
      reflexivity.
    + rewrite <- IHx.
      rewrite -> Bool.negb_involutive.
      simpl.
      reflexivity.
Qed.









Theorem sqrt2_is_irrational: forall p q: nat,
  p*p <> 2*q*q.

Proof.
  intros.
  intros eq.
  assert (Nat.even (p*p) = true).
  {
    rewrite -> eq.
    rewrite <- Nat.mul_assoc.
    apply x_times_2_is_even.
  }

  assert (Nat.even p = true).
  {
    rewrite square_even_is_even in H.
    apply H.
  }

  apply even_exists in H0.
  destruct H0 as [p' Hp'].
  rewrite <- Hp' in eq.


  Set Printing All
