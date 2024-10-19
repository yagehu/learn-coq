Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d : day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb_1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb_2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb_3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb_4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb_5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b : bool) : bool :=
  if b
  then false
  else true.

Definition andb' (b1 : bool) (b2 : bool) : bool :=
  if b1
  then b2
  else false.

Definition orb' (b1 : bool) (b2 : bool) : bool :=
  if b1
  then true
  else b2.

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
    | true =>
      match b2 with
        | true => false
        | false => true
      end
    | false => true
  end.

Example test_nandb_1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb_2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb_3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb_4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  match b1 with
    | true =>
      match b2 with
        | true => b3
        | false => false
      end
    | false => false
  end.

Example test_andb3_1: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb3_2: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb3_3: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb3_4: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
    | black => true
    | white => true
    | primary p => false
  end.

Definition is_red (c : color) : bool :=
  match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
  end.

Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo : rgb.
Check foo : bool.

Module TuplePlayground.
  Inductive bit : Type :=
    | B1
    | B0.

  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).

  Check (bits B1 B0 B1 B0) : nybble.

  Definition all_zero (nb : nybble) : bool :=
    match nb with
      | (bits B0 B0 B0 B0) => true
      | (bits _ _ _ _) => false
    end.

  Compute (all_zero (bits B1 B0 B1 B0)).
  Compute (all_zero (bits B0 B0 B0 B0)).
End TuplePlayground.

Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
      | O => O
      | S n' => n'
    end.

