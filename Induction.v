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

Check leb.

Theorem plus_leb_compat_l:
  forall n m p : nat, n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [ | p' IHp'].
  - simpl.
    rewrite H.
    reflexivity.
  - simpl.
    rewrite IHp'.
    reflexivity.
Qed.

Theorem leb_refl:
  forall n:nat, (n <=? n) = true.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem zero_neqb_S:
  forall n : nat, 0 =? (S n) = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem andb_false_r:
  forall b : bool, andb b false = false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem S_neqb_0:
  forall n : nat, (S n) =? 0 = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_1_l:
  forall n : nat, 1 * n = n.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - reflexivity.
  - simpl.
    rewrite add_0_r.
    reflexivity.
Qed.

Theorem all3_spec:
  forall b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem mult_plus_distr_r:
  forall n m p : nat, (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [ | n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem mult_assoc:
  forall n m p: nat, n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [ | n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.

Theorem add_shuffle3':
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite -> add_comm.
    reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin): bin :=
  match m with
    | Z => B1 Z
    | B0 n => B1 n
    | B1 n => B0 (incr n)
  end.

Fixpoint bin_to_nat (m: bin): nat :=
  match m with
    | Z => O
    | B0 n' => 2 * (bin_to_nat n')
    | B1 n' => S (2 * (bin_to_nat n'))
  end.

Compute bin_to_nat Z.
Compute bin_to_nat (B0 Z).
Compute bin_to_nat (B1 Z).
Compute bin_to_nat (B1 (B1 Z)).

Theorem bin_to_nat_pres_incr: forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [ | b0 IH0 | b1 IH1].
  - simpl. reflexivity.
  - simpl.
    rewrite -> add_0_r.
    replace (bin_to_nat b0 + bin_to_nat b0 + 1) with (1 + bin_to_nat b0 + bin_to_nat b0).
    + rewrite -> plus_n_Sm.
      rewrite <- IH0.
      reflexivity.
    + rewrite <- add_assoc.
      rewrite -> add_comm.
      reflexivity.
  - simpl.
    rewrite -> add_0_r.
    rewrite -> add_0_r.
    rewrite -> IH1.
    rewrite -> plus_n_Sm.
    simpl.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n: nat): bin :=
  match n with
    | O => Z
    | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat: forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [ | n' IH'].
  - simpl. reflexivity.
  - simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IH'.
    reflexivity.
Qed.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Definition double_bin (b: bin) : bin :=
  match b with
    | Z => Z
    | B0 b' => B0 (B0 b')
    | B1 b' => B0 (B1 b')
  end.

Example double_bin_zero: double_bin Z = Z.
Proof. reflexivity. Qed.

Lemma double_incr_bin:
  forall b, double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b.
  induction b as [ | b0 IH0 | b1 IH1].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fixpoint normalize (b: bin) : bin :=
  match b with
    | Z => Z
    | B0 b' => double_bin (normalize b')
    | B1 b' => B1 (normalize b')
  end.

Example normalize_zeros: normalize (B0 (B0 Z)) = Z.
Proof. simpl. reflexivity. Qed.

Theorem bin_nat_bin: forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  assert (H: forall n: nat, double_bin (nat_to_bin n) = nat_to_bin (double n)).
    {
      induction n as [ | n' IHn'].
      + reflexivity.
      + simpl.
        rewrite -> double_incr_bin.
        rewrite -> IHn'.
        reflexivity.
    }
  induction b as [ | b0 IH0 | b1 IH1].
  - simpl. reflexivity.
  - simpl.
    rewrite add_0_r.
    rewrite <- IH0.
    replace (bin_to_nat b0 + bin_to_nat b0) with (double (bin_to_nat b0)).
    + replace (nat_to_bin (double (bin_to_nat b0))) with (double_bin (nat_to_bin (bin_to_nat b0))).
      * reflexivity.
      * rewrite -> H.
        reflexivity.
    + rewrite -> double_plus.
      reflexivity.
  - simpl.
    rewrite -> add_0_r.
    rewrite <- double_plus.
    rewrite <- H.
    rewrite -> IH1.
    assert (H': forall b: bin, incr (double_bin b) = B1 b).
      {
        induction b as [ | b0' IH0' | b1' IH1'].
        - simpl. reflexivity.
        - reflexivity.
        - reflexivity.
      }
    rewrite -> H'.
    reflexivity.
Qed.
