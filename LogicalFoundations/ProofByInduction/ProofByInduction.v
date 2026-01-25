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
(** Informal proofs are algorithms; formal proofs are code.

    A proof of a mathematical proposition P is a written text that instills in the reader or hearer the certainty that P is true.

    That is, a proof is an act of communication.

    Acts of communication may involve different sorts of readers.
    On the one hand, the "reader" can be a program like Rocq, in which case the "belief" that is instilled is that P can be mechanically derived from a certain set of formal logical rules, and the proof is a recipe that guides the program in checking this fact.

    Alternatively, the reader can be a human being, in which case the proof will probably be written in English or some other natural language and will thus necessarily be informal.

    Here a valid proof is one that makes the reader believe P. But the same proof may be read by many different readers, some of whom may be convinced by a particular way of phrasing the argument, while others may not be.

    For the inexperienced readers, the only way to convince them will be to make the argument in painstaking detail; while other readers, may find all this detail so overwhelming.

    There is no universal standard.

    Mathematicians have developed a rich set of conventions and idioms for writing about complex mathematical objects and make communication fairlhy reliable.

    Formal proof is very inefficient to communicate with human.*)

(** Theorem : (n =? n) = true for any n.
    We do induction on n
    if n = 0, then we have 0 =? 0 which implies true.
    if n = S n' with the induction hypothesis n' =? n' then we have S n' =? S n',
    for S n' =? S n' it is same as n' =? n', where we finish the proof by using the induction hypothesis.*) 

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  replace (n + (m + p)) with ((n + m) + p).
  (* Need parenthesis to avoid confusion. *) 
  - replace (m + (n + p)) with ((m + n) + p).
    -- replace (n + m) with (m + n).
       --- reflexivity.
       --- rewrite <- add_comm. reflexivity.
    -- rewrite <- add_assoc. reflexivity.
  - rewrite <- add_assoc. reflexivity.
Qed.

Theorem mul_1_r : forall n : nat,
  n * 1 = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem S_add_1_r : forall n : nat,
  S n = n + 1.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'.
    replace (S (n' + 1)) with (n' + 1 + 1).
    -- reflexivity.
    -- rewrite plus_n_Sm. rewrite <- add_assoc. reflexivity.
Qed.

Theorem S_add_r : forall n m : nat,
  S n + m = n + S m.
Proof.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    -- rewrite add_comm. reflexivity.
    -- reflexivity.  
  - induction m as [| m' IHm'].
    -- rewrite add_0_r. rewrite <- S_add_1_r. reflexivity.
    -- rewrite -> IHn'. simpl. rewrite S_add_1_r. rewrite S_add_1_r.
       replace (n' + S m' + 1 + 1) with (n' + (S m' + 1) + 1).
       --- replace (S m' + 1) with (S (S m')).
           ---- rewrite <- add_assoc.
                replace (S (S m') + 1) with (S (S (S m'))).
                ----- reflexivity.
                ----- rewrite S_add_1_r. reflexivity.
           ---- rewrite S_add_1_r. reflexivity.
       --- rewrite add_assoc. reflexivity.
Qed.

Theorem plus_m_Sn : forall n m : nat,
  S (n + m) = S n + m.
Admitted.

Theorem mul_add_S_l : forall n m : nat,
  n * S m = n + n * m.
Proof.
  induction n as [| n' IHn'].
  -- induction m as [| m' IHm'].
     --- reflexivity.
     --- reflexivity.
  -- induction m as [| m' IHm'].
     --- simpl. rewrite -> mul_1_r. rewrite -> mul_0_r. rewrite -> add_0_r. reflexivity.
     --- rewrite -> S_add_r. simpl. rewrite IHn'. rewrite plus_m_Sn. rewrite <- S_add_r. rewrite <- S_add_r. rewrite -> plus_m_Sn. simpl. rewrite add_assoc. rewrite add_assoc.
         replace (m' + n') with (n' + m').
         ---- reflexivity.
         ---- rewrite add_comm. reflexivity.
Qed.

Theorem mul_comm : forall m n : nat, 
  m * n = n * m.
Proof.
  intros m n.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    -- reflexivity.
    -- simpl. rewrite -> IHm'. reflexivity.
  - induction m as [| m' IHm'].
    -- simpl. rewrite <- IHn'. reflexivity.
    -- simpl. replace (n' + (m' * S n')) with (m' + S m' * n').
       --- rewrite -> IHn'. reflexivity.
       --- simpl. rewrite -> add_assoc.
           replace (m' + n') with (n' + m').
           ---- rewrite <- add_assoc.
                replace (m' + m' * n') with (m' * S n').
                ----- reflexivity.
                ----- induction n' as [| n'' IHn''].
                      ** induction m' as [| m'' IHm''].
                         *** reflexivity.
                         *** simpl. rewrite mul_0_r. rewrite -> mul_1_r. rewrite -> add_0_r. reflexivity.
                      ** rewrite mul_add_S_l. reflexivity.
           ---- rewrite add_comm. reflexivity.
Qed.

