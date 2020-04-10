From LF Require Export Basics.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [|n' hn'].
  - reflexivity.
  - simpl. rewrite <- hn'. reflexivity. Qed.

(* how one does a rewrite exactly in one place? first occurence? eg the situation above, without <- *)

 Theorem minus_diag : forall n,
    minus n n = 0.
 Proof.
   induction n as [|n' hn']. (* induction automatically introduces variables that are quantified *)
   - reflexivity.
   - simpl. exact hn'. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [|n' hn'].
  - reflexivity.
  - simpl. exact hn'. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [|n' hn'].
  - reflexivity.
  - simpl. rewrite hn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [ | n' hn'].
  - simpl. induction m as [|m' hm'].
    + reflexivity.
    + simpl. rewrite <- hm'. reflexivity.
  - simpl. induction m as [|m' hm'].
    + simpl. rewrite hn'. reflexivity.
    + simpl. rewrite <- hm', hn', hn'. simpl. reflexivity. Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' hn].
  - reflexivity.
  - simpl. rewrite hn. reflexivity. Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n'=> S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n as [|n' hn].
  - reflexivity.
  - simpl. rewrite plus_comm, hn. reflexivity. Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n as [|n' hn].
  - simpl. reflexivity.
  - rewrite hn, negb_involutive. simpl. reflexivity. Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. } (* !!! inline theorems! !! *)
                         (* or assert (0 + n = n) as H *)
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. } (* why can't it work like in Lean? *)
  rewrite -> H. reflexivity. Qed.

