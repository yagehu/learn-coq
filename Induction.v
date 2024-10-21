From LF Require Export Basics.

Theorem add_0_r_first_try: forall n : nat, n + 0 = n.
Proof. intros n. simpl. Abort.

Theorem add_0_r: forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem minus_n_n: forall n : nat, minus n n = 0.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - reflexivity.
  - rewrite <- IHn'.
    reflexivity.
Qed.

Theorem mul_0_r: forall n : nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm:
  forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem add_comm: forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [ | n' IHn'].
  - rewrite -> add_0_r.
    simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem add_assoc:
  forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [ | n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> plus_n_Sm.
    rewrite <- IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n : nat, double n = n + n.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem eqb_refl: forall n : nat, (n =? n) = true.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem even_S: forall n : nat, even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - reflexivity.
  - rewrite -> IHn'.
    simpl.
    rewrite -> negb_involutive.
    reflexivity.
Qed.

Theorem mult_0_plus':
  forall n m : nat, (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    - rewrite -> add_comm.
      simpl.
      rewrite -> add_comm.
      reflexivity.
  - rewrite -> H.
    reflexivity.
Qed.

Theorem add_shuffle3:
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  assert (H: n + m = m + n -> n + m + p = m + n + p).
  - intros H.
    rewrite -> H.
    reflexivity.
  - rewrite -> H.
    reflexivity.
    rewrite <- add_comm.
    reflexivity.
Qed.

Theorem mul_m_Sn:
  forall m n : nat, m * (S n) = m + m * n.
Proof.
  intros m n.
  induction m as [ | m' IHm'].
  - reflexivity.
  - simpl.
    rewrite -> add_assoc.
    assert (H: m' + n = n + m').
    + rewrite add_comm. reflexivity.
    + rewrite -> H.
      rewrite -> IHm'.
      rewrite -> add_assoc.
      reflexivity.
Qed.

Theorem mul_comm: forall m n : nat, m * n = n * m.
Proof.
  intros m n.
  induction m as [ | m' IHm'].
  - rewrite -> mul_0_r.
    reflexivity.
  - assert (H: n * S m' = n + n * m').
    + rewrite -> mul_m_Sn.
      reflexivity.
    + rewrite -> H.
      simpl.
      rewrite IHm'.
      reflexivity.
Qed.
