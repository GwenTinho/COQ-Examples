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

Lemma next_even_is_odd : forall x : nat,
  Nat.even x = negb (Nat.even (S x)).
Proof.
  intros.
  induction x.
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHx.
    rewrite -> Bool.negb_involutive.
    reflexivity.
Qed.

Lemma cancel_negb : forall a b: bool,
  negb a = negb b -> a = b.
Proof.
  intros.
  destruct a.
  - destruct b.
    + reflexivity.
    + simpl in H.
      symmetry.
      apply H.
  - destruct b.
    + simpl in H.
      symmetry.
      apply H.
    + reflexivity.
Qed.

Lemma even_is_xor: forall x y : nat,
  Nat.even (x+y) = negb (xorb (Nat.even x) (Nat.even y)).
Proof.
  intros.
  induction x.
  - simpl.
    case (Nat.even y); reflexivity.
  - rewrite next_even_is_odd in IHx.
    rewrite (next_even_is_odd x) in IHx.
    apply cancel_negb in IHx.
    rewrite Nat.add_succ_l.
    rewrite -> IHx.
    clear IHx.
    rewrite Bool.negb_xorb_l.
    reflexivity.
Qed.

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


Lemma cancel_2: forall x y : nat,
  2 * x = 2 * y -> x = y.
Proof.
  intros.
  lia.
Qed.


Theorem sqrt2_infinite_descent: forall p q,
 q <> 0 -> p*p = 2*q*q -> exists pp qq : nat,
 pp * pp = 2 * qq * qq /\ qq < q.
Proof.
  intros p q qnz eq.
  assert (eq' := eq).

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
  repeat rewrite <- Nat.mul_assoc in eq.
  apply cancel_2 in eq.
  rewrite Nat.mul_comm in eq.
  clear H.

  assert (Nat.even (q*q) = true).
  {
    rewrite <- eq.
    rewrite <- Nat.mul_assoc.
    apply x_times_2_is_even.
  }

  assert (Nat.even q = true).
  {
    rewrite square_even_is_even in H.
    apply H.
  }

  apply even_exists in H0.
  destruct H0 as [q' Hq'].
  rewrite <- Hq' in eq.
  repeat rewrite <- Nat.mul_assoc in eq.
  apply cancel_2 in eq.
  symmetry in eq.
  rewrite Nat.mul_comm in eq.
  clear H.
  symmetry in eq.

  assert (q > q').
  lia.
  clear Hp' Hq'.

  exists p'.
  exists q'.

  split.
  - apply eq.
  - apply H.
Qed.

Definition lt_nat (p q : nat*nat) := snd p < snd q.

Theorem lt_wf: well_founded lt_nat.
Proof.
  unfold well_founded.
  intros.

Admitted.

Theorem infinite_descent: forall P : Prop -> forall p q : nat,
  (P p q) -> exists p' q' : nat, (f p' q') /\ q' < q ->.
Proof.

Qed.


Theorem sqrt2_is_irrational: forall p q: nat,
  q <> 0 -> p*p <> 2*q*q.
Proof.
  intros p q qnz.
  unfold not.
  intros eq.
  generalize sqrt2_infinite_descent.
  intros.
  specialize (H p q).
  apply H in qnz.
  destruct qnz.
  destruct H0.
  destruct H0.
  2 : {
    apply eq.
  }
  clear H.



Qed.

  Set Printing All
