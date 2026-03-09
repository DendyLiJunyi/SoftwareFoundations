From LogicalFoundations Require Export Poly.

(** The propositions and proofs we worked on so far depends on the equality propositions(e1 = e2). 

   Being a proposition neq being provable. 

   Propositions can appear in Theomrem declarations. *)

(** just give names to expressions *)
Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim.

Theorem plus_claim_is_true : plus_claim.
Proof.
  unfold plus_claim.
  reflexivity.
Qed.

(** fun x => Prop is said to defined properies. *)

Definition injective {A B} (f : A -> B) : Prop := forall x y : A, f x = f y -> x = y.

Check injective.

Lemma succ_inj : injective S.
Proof.
  unfold injective.
  intros x y H.
  injection H as H1.
  apply H1.
Qed.
(** So the type is just injective S, which is a type denote the property of S.

   = is a binary function returns a Prop. 

   = is the syntactic sugar for eq. *)

Check @eq.

(** * Logicla Connectives * **)
(** ** Conjunction ** **)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  + (* 3 + 4 = 7 *)
    reflexivity.
  + (* 2 * 2 = 4 *)
    reflexivity.
Qed.

Check @conj.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  + (* 3 + 4 = 7 *)
    reflexivity.
  + (* 2 * 2 = 4 *)
    reflexivity.
Qed.

Example plus_is_0 :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  induction n as [n | n' IH].
  - (* n = 0 *)
    intros m H.
    split.
    + reflexivity.
    (* apply can also do simpl. *)
    + apply H.
  - (* n = S n' *)
    intros m H.
    apply conj.
    + discriminate.
    + discriminate.
Qed.

(** destruct conjunctive hypothesis. *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [H1 H2] eqn:E.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

(** It's a little different to handle A -> B -> C and A /\ B -> C. *)
Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** Why do we need conjunction since conjunction A /\ B -> = A -> B -> 

   conjunctions often arise form intermiediate steps in proofs. *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply plus_is_0 in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** use underscore to throw away unused hypothesis. *)
Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. 
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [_ Hq].
  apply Hq.
Qed.

(** rearrange the order of conjunctions. *)
Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* can directly pattern matching? *)
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Check and.

(** ** Disjunction ** **)

