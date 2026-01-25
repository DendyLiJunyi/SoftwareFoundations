From Stdlib Require Export Arith.
From LogicalFoundations Require Export Basics.

Theorem add_0_r_firsttry : forall n : nat, n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem add_0_r_secondtry : forall n : nat, n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

(** We can further destruct n', since n' can be arbitrarily large, this doesn't work.
    The more powerful reasoning principle we need is induction.
    - show P(0) holds
    - show for any n', if P(n') holds, then so does P(S n')
    - conclude that P(n) holds for all n.*)

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n : nat, n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    -- reflexivity.
    -- reflexivity.
  - induction m as [| m' IHm'].
    -- simpl. rewrite -> IHn'. reflexivity.
    -- simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    -- reflexivity.
    -- simpl. rewrite <- IHm'. reflexivity.
  - induction m as [| m' IHm'].
    -- simpl. rewrite -> IHn'. reflexivity.
    -- simpl. rewrite -> IHn'. rewrite <- IHm'. simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n as [| n' IHn'].
  - induction m as [| m'].
    -- induction p as [| p'].
       --- reflexivity.
       --- reflexivity.
    -- induction p as [| p'].
       --- reflexivity.
       --- reflexivity.
  - induction m as [| m'].
    -- induction p as [| p' IHp'].
       --- simpl. rewrite <- IHn'. reflexivity.
       --- simpl. rewrite <- IHn'. reflexivity.
    -- induction p as [| p' IHp'].
       --- simpl. rewrite <- IHn'. reflexivity.
       --- simpl. rewrite <- IHn'. reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat, (n =? n) = true.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem negb_negb : forall a : bool, negb (negb a) = a.
Proof.
  intro a.
  destruct a as [|] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem even_S : forall n : nat, even (S n) = negb (even n).
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> negb_negb. reflexivity.
Qed.

(** Large proofs are often broken into a sequence of theorems, with later proofs referring to earier theorem.

    Use the require fact in place and then prove it as a separate step.*)

Theorem mult_0_plus' : forall n m : nat, (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  replace (n + 0 + 0) with n.
  - reflexivity.
  - rewrite add_comm. simpl. rewrite add_comm. reflexivity.
Qed.

(** tactic replace e1 with e2 introduce two subgoals:
    - e1 is replaced by e2
    - e1 = e2*)

(** rewrite is not smart at all.*)

Theorem plus_rearrange_firsttry : forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite add_comm.
  (* Doesn't work... Rocq rewrites the biggest expression. *)
Abort.

Theorem plus_rearrange : forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite add_comm. reflexivity.
Qed.

(** * Foraml vs. Informal Proof * **)
(** Informal proofs are algorithms; formal proofs are code.*)


