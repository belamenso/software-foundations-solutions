Inductive day: Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
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
Compute (next_weekday (next_weekday friday)).

Example test_next_weekday: (next_weekday (next_weekday friday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool: Type := true | false.

Definition negb (b: bool) : bool :=
match b with
  | true => false
  | false => true
end.

Definition andb (b_1 : bool) (b_2: bool): bool :=
match b_1 with
  | true => b_2
  | false => false
end.

Definition orb (b_1 : bool) (b_2: bool): bool :=
match b_1 with
  | true => true
  | false => b_2
end.


Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x || y" := (orb x y).
Notation "x && y" := (andb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.


Definition nandb (b1:bool) (b2:bool) : bool :=
match (b1, b2) with
  | (true, true) => false
  | _ => true
end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
match b1, b2, b3 with
  | true, true, true => true
  | _,_,_ => false (* or do (x,y) and match with _ or do x,y and do _,_ *)
end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check (negb true).
Check negb.

Inductive rgb: Type := red | green | blue.

Inductive color: Type := black | white | primary (p: rgb).

Definition monochrome (c: color): bool :=
match c with primary _ => false | _ => true end.

Definition isred (c: color): bool :=
match c with
  | primary red => true
  | _ => false
end.

Module NatPlayground.

Inductive nat: Type := O | S (n: nat). (* letter O not 0 *)

Definition pred (n: nat) : nat :=
match n with
  | O => O
  | S n' => n'
end.

End NatPlayground.

Check S (S (S O)). (* wow it prints it in a decimal form! *)

Fixpoint evenb (n: nat) : bool :=
match n with
  | 0 => true
  | S 0 => false
  | S(S n') => evenb n'
end.

Definition oddb (n: nat): bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n m:nat): nat :=
match n with
  | 0 => m
  | S n' => S (plus n' m)
end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
match n with
  | 0 => 0
  | S n' => plus m (mult n' m)
end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Fixpoint exp (base power : nat) : nat :=
match power with
    | O => S O
    | S p => mult base (exp base p)
end.

Fixpoint factorial (n:nat) : nat :=
match n with 0 => 1 | S n' => mult n (factorial n') end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1).

Fixpoint eqb (n m : nat) : bool :=
match n, m with
  | 0, 0 => true
  | S n, S m => eqb n m
  | _, _ => false
end.

Fixpoint leb (n m : nat) : bool :=
match n, m with
  | 0, _ => true
  | S n, S m => leb n m
  | _, _ => false
end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
match m with
  | 0 => false
  | S m' => leb n m'
end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intro n. reflexivity. Qed.

(* reflexivity expands definitions since it finishes the proof,
simpl is just a step so it doesn't mess up the state without our permission. *)

(* Example Theorem Lemma Remark Fact  mean almost the same *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0. (* _l suffix means "on the left" *)
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat, n = m -> n + n = m + m.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o Eq_nm Eq_mo.
  rewrite <- Eq_mo. rewrite -> Eq_nm. reflexivity. Qed.

(* Admitted command means believe it *)

Theorem mult_0_plus : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m. rewrite plus_O_n. reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m H.
  rewrite plus_1_l, H. reflexivity. Qed. (* !!! multiple rewrites !! *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
(* command Abort means give up for a minute *)
  destruct n as [|n'] eqn:E. (* you may leave off eqn:E, then the assumption (from the case-split) named E will not be added to your list *)  
  - reflexivity. (* - "focuses" the goal *)
  - reflexivity. (* remember, reflexivity itself uses some simplification *)
Qed.

(* - are called bullets, not needed, but they separate, you do not want 
Coq to interpret proof boundaries differently than you! *)

Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
  intros b. destruct b (*as [|]*). (* you can ommit empty lists like these *)
  { reflexivity. }
  - reflexivity. Qed.

(* no []s or [] or [|] are ok here *)
(* bullets nest, first - then + then * then just braces: {} *)
(* you can use braces any time though, and they obviously allow you to reuse the bullet shapes. *)

(* shorthand: intro + destruct *)

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

(* shorthand intro + destruct no names *)
Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] [] E.
  - reflexivity.
  - exact E.
  - reflexivity.
  - exact E. Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

(* Coq's 0%nat 0%Z notation *)

(* for Fixpoint, coq requires that for all Fixpoint definitions, some
arugument is structurally decreasing *)

(*
Fixpoint wont_compile (n: nat) (flag: bool): nat :=
match n,flag with
  | 0,_ => 0
  | _, true => wont_compile (minus n 2) false
  | _, false => wont_compile (plus n 1) true
end.
*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite H, H. reflexivity. Qed.

From Coq Require Export String.
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite H, H, negb_involutive. reflexivity. Qed.

Theorem andb_eq_orb :
  forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros [] c H.
  - simpl in H. rewrite H. reflexivity.
  - simpl in H. exact H. Qed.

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
match m with
  | Z => B Z
  | A m' => B m'
  | B m' => A (incr m')
end.
 
Fixpoint bin_to_nat (m:bin) : nat :=
match m with
  | Z => 0
  | A m' => 2 * bin_to_nat m'
  | B m' => 1 + 2 * bin_to_nat m'
end.

Example test_bin_incr1: bin_to_nat (incr (A (B Z))) = 1 + bin_to_nat (A (B Z)).
Proof. reflexivity. Qed.
Example test_bin_incr2: bin_to_nat (incr (A (A (B Z)))) = 1 + bin_to_nat (A (A (B Z))).
Proof. reflexivity. Qed.
Example test_bin_incr3: bin_to_nat (incr (B (A (B Z)))) = 1 + bin_to_nat (B (A (B Z))).
Proof. reflexivity. Qed.
Example test_bin_incr4: bin_to_nat (incr (A (B (B Z)))) = 1 + bin_to_nat (A (B (B Z))).
Proof. reflexivity. Qed.
Example test_bin_incr5: bin_to_nat (incr (B(B(A (B (B Z)))))) = 1 + bin_to_nat (B(B(A (B (B Z))))).
Proof. reflexivity. Qed.

