From LogicalFoundations Require Export Poly.
From LogicalFoundations Require Export ProofByInduction.

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
Check or.

Lemma factor_is_O :
  forall n m : nat,
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* case analysis pattern *)
  intros n m [Hn | Hm].
  - (* n = 0 *)
    rewrite -> Hn.
    reflexivity.
  - (* m = 0 *)
    rewrite -> Hm.
    apply Nat.mul_0_r.
Qed.

(** Show disjunction holds, it suffices to show that one of its sides holds. *)

Lemma or_intro_l : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zeor_or_succ : 
  forall n : nat,
  n = 0 \/ n = S (pred n).
Proof.
  intros [| n'].
  - (* n = 0 *) 
    left. reflexivity.
  - (* n = S n' *)
    right. reflexivity.
Qed.

Lemma mult_is_0 :
  forall n m,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [| n'] [| m'] H.
  - (* n = 0 & m = 0 *)
    left. reflexivity.
  - (* n = 0 & m = S m' *)
    left. reflexivity.
  - (* n = S n' & m = 0 *)
    right. reflexivity.
  - (* n = S n' & m = S m' *)
    discriminate.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(** ** Falsehood and Negation ** **)

(** If P satisfies the principle of exploision, then forall Q, P -> Q *)

(** False is un-provable. *)
Definition not (P : Prop) := P -> False.

Check False.

Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet :
  forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  (* Why destruct contra can complete every goal? *)
  destruct contra.
Qed.

Theorem not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P HnotP Q HP.
  unfold not in HnotP.
  apply HnotP in HP.
  destruct HP.
Qed.

(** Inforaml:
   P is true
   P -> False is true
   So we have a contradiction. *)

Notation "x <> y" := (~(x = y)) : type_scope.

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  (* Assume oppsite is equal. *)
  intros H.
  discriminate H.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed.

(** double_neg_informal:

   Unfold ~~P as (P → False) → False.

   Assume P. We must show (P → False) → False.

   Assume ¬P (i.e. P → False).

   Apply ¬P to our assumption P — this directly gives False.

   Therefore (P → False) → False, i.e. ~~P. 

    We are inside the world of type theory not Mathematic Logic! *)

(** How to understand implication in typetheory? *)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  (* Assume P -> Q, Assume not Q. *)
  intros P Q H1 H2.
  unfold not.
  unfold not in H2.
  (* Assume P. *)
  intros HP.
  apply H1 in HP.
  apply H2 in HP.
  destruct HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~ P).
Proof.
  intros P.
  unfold not.
  intros [HP HnotP].
  apply HnotP in HP.
  destruct HP.
Qed.

(** not_PNP_informal
   By definition not (P and not P) is (P and P -> False) -> False.

   Assume P and P -> False, we need to show False.

   By P and P -> False we assume False, thus we have proved. *)

Theorem de_morgan_not_or : forall (P Q : Prop),
  ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  intros P Q.
  unfold not.
  intros H.
  split.
  - intros HP.
    apply H.
    left. apply HP.
  - intros HQ.
    apply H.
    right. apply HQ.
Qed.

Lemma not_S_pred_n : ~ (forall n : nat, S (pred n) = n).
Proof.
  unfold not.
  intros H.
  specialize H with (n := 0).
  (* 0 has no pred. *) 
  discriminate H.
Qed.

(** ex_falso_quodlibet can change the goal to false. *)
Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* note implicit destruct b here! *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(** ** Truth ** **)
(** I is the constant for True. *)
Lemma True_is_true : True.
Proof. apply I. Qed.

(** True is useful when defining complex Props. *)
Definition disc_fn (n : nat) : Prop :=
  match n with
  | 0 => True
  | S _ => False
  end.

Theorem disc_example : forall n,
  ~ (0 = S n).
Proof.
  intros n contra.
  (* assume a fact. *)
  assert (H : disc_fn 0). { simpl. apply I. }
  (* rewrite the fact by a contradiction. *)
  rewrite contra in H.
  (* obtain another fact. *)
  simpl in H.
  apply H.
Qed.

(** Since two constructors are not the same, when we have an equality states two constructors are same, we can use pattern matching skill to define one of them to be true another one to be false. *)
Definition disc_fn' {X : Type} (x : list X) : Prop :=
  match x with
  | nil => True
  | x :: xs => False
  end.

Theorem nil_is_not_cons : forall X (x : X) (xs : list X),
  ~ (nil = x :: xs).
Proof.
  intros X x xs.
  unfold not.
  intros H.
  assert (H1 : @disc_fn' X nil). { apply I. }
  rewrite -> H in H1.
  simpl in H1.
  apply H1.
Qed.

(** ** Logical Equivalence ** **)
(** Print is used to print all the related information. *)
Print "<->".

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  unfold iff.
  split.
  - apply HBA.
  - apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false'.
  - intros H. rewrite -> H. unfold not. intros H'. discriminate H'.
Qed.

(** apply with <->. *)
Lemma apply_iff_example1 :
  forall P Q R : Prop,
  (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R [HPQ HQP] HQR HP.
  apply HQR. apply HPQ. apply HP.
Qed.

Lemma apply_iff_example2 :
  forall P Q R : Prop,
  (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R [HPQ HQP] HPR HQ.
  apply HPR. apply HQP. apply HQ.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  unfold iff.
  split.
  - intros H. apply H.
  - intros H. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [HPQ HQP] [HQR HRQ].
  split.
  - (* P -> R *)
    intros HP.
    apply HPQ in HP.
    apply HQR in HP.
    apply HP.
  - (* R -> P *)
    intros HR.
    apply HRQ in HR.
    apply HQP in HR as HP.
    apply HP.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros HPQR.
    split.
    + destruct HPQR as [HP | HQR].
      ++ left. apply HP.
      ++ destruct HQR as [HQ HR].
         +++ right. apply HQ.
    + destruct HPQR as [HP | HQR].
      ++ left. apply HP.
      ++ destruct HQR as [HQ HR].
         right. apply HR.
  - intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. split.
      ++ apply HQ.
      ++ apply HR.
Qed.

