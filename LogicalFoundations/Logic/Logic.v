From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Classes.Morphisms_Prop.
From LogicalFoundations Require Export Poly.
From LogicalFoundations Require Export ProofByInduction.
From LogicalFoundations Require Export Tactics.

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


(** ** Setoids and Logical Equivalence ** **)
(** setoid is a set equipped with an equivalence relation. 

   reflexive;
   symmetric;
   transitive;

   This allows us to rewrite when x = y.

   Since <-> is an equivalence relation, we can also use rewrite on it. *)

Lemma mul_eq_0 : forall n m,
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros n m.
  split.
  - intro H.
    + destruct n as [| n'].
      ++ left. reflexivity.
      ++ right. destruct m as [| m'].
         +++ reflexivity.
         +++ discriminate H.
  - intros [Hn | Hm].
    + rewrite -> Hn. reflexivity.
    + rewrite -> Hm. apply mul_0_r.
Qed.

Theorem or_assoc :
  forall P Q R : Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [HP | [HQ | HR]].
    + left. left. apply HP.
    + left. right. apply HQ.
    + right. apply HR.
  - intros [[HP | HQ] | HR].
    + left. apply HP.
    + right. left. apply HQ.
    + right. right. apply HR.
Qed.

(** rewrite on <-> *)
Lemma mul_eq_0_ternary :
  forall n m p,
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0.
  rewrite mul_eq_0.
  rewrite <- or_assoc.
  reflexivity.
Qed.

(** ** Existential Quantification ** **)
(** To prove a statement of exists x, P, we must show P holds for some specific choice for x(witness of the existential.) *)

Definition Even x := exists n : nat,
  x = double n.
Check Even : nat -> Prop.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even.
  exists 2.
  reflexivity.
Qed.

(** existential hypothesis can be destructed. *)
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  rewrite -> Hm.
  exists (2 + m).
  reflexivity.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros [x Hx].
  specialize H with (x := x).
  apply Hx in H.
  apply H.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.

Theorem leb_geb_eq : forall n m, (S n <=? m) = false /\ (n <=? m) = true -> n = m.
Proof.
  induction n as [| n' IH].
  - induction m as [| m' IHm].
    + reflexivity.
    + intros [H1 H2].
      simpl in H1. discriminate H1.
  - induction m as [| m' IHm].
    + intros [H1 H2].
      simpl in H2. discriminate.
    + intros [H1 H2].
      simpl in H2, H1.
      f_equal.
      apply IH. split.
      ++ apply H1.
      ++ apply H2.
Qed.

Theorem leb_plus_exists : forall n m, n <=? m = true ->
  exists x, m = n + x.
Proof.
  intros [| n'].
  - induction m as [| m' IH].
    + exists 0. 
      reflexivity.
    + intros H. exists (S m'). reflexivity.
  - induction m as [| m' IH].
    + intros H.
      simpl in H. discriminate H.
    + intros H. simpl in H. destruct (S n' <=? m') eqn:E.
      ++ assert (I : true = true). { reflexivity. } apply IH in I. destruct I as [x Hx]. exists (S x). rewrite -> Hx. simpl. f_equal. symmetry. apply Nat.add_succ_r.
      ++ assert (eq : m' = n'). { symmetry. apply leb_geb_eq. split. apply E. apply H. }
         exists 0. rewrite <- eq. simpl. rewrite add_0_r. reflexivity.
Qed.

(** from two things which haven't got a direct connection, one need to use induction to build the connection. *)

Theorem leb_refl : forall n,
  n <=? n = true.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. apply IH.
Qed.

Theorem leb_increase : forall n m,
  n <=? n + m = true.
Proof.
  induction n as [| n' IH].
  - induction m.
    + reflexivity.
    + reflexivity.
  - intros m.
    simpl. apply IH.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n + x) -> n <=? m = true.
Proof.
  (* forget to make the induction hypothesis general! *)
  intros n m [x H].
  induction n as [| n' IH].
  - destruct m as [| m'].
    + reflexivity.
    + reflexivity.
  - induction m as [| m'].
    + discriminate H.
    + rewrite -> H. simpl in H. injection H as H1. simpl. destruct x as [| x'].
      ++ rewrite add_0_r. apply leb_refl.
      ++ simpl. apply leb_increase.
Qed.

(** better way make the induciton more general! *)
Theorem leb_plus_exists' : forall n m, n <=? m = true -> exists x, m = n + x.
Proof.
  induction n as [| n' IH].
  - intros m _. exists m. reflexivity.
  - intros m H. destruct m as [| m'].
    + simpl in H. discriminate.
    + simpl in H. apply IH in H. destruct H as [x Hx].
      exists x. simpl. rewrite Hx. reflexivity.
Qed.

Theorem plus_exists_leb' : forall n m, (exists x, m = n + x) -> n <=? m = true.
Proof.
  induction n as [| n' IH].
  - intros m _. reflexivity.
  - intros m [x Hx]. destruct m as [| m'].
    + simpl in Hx. discriminate.
    + simpl. apply IH. exists x. simpl in Hx. injection Hx as Hx'. apply Hx'.
Qed.

(** * Programming with Propositions * **)

(** Defining complex propositions from simpler ones. *)

(** An element x occurs in a list l. *)
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x = x' \/ In x l'
  end.

(* Prove a proposition. *)
Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  intros n. intros P. unfold In in P. destruct P as [P1 | [P2 | P3]].
  - exists 1. rewrite -> P1. reflexivity.
  - exists 2. rewrite -> P2. reflexivity.
  - exfalso. apply P3.
Qed.

(** A statement is formally written doesn't mean it is provable. *)
Example In_example_2' :
  forall n, In n [1; 4] ->
  exists n', n = 2 * n'.
Proof.
Abort.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l ->
  In (f x) (map f l).
Proof.
  intros A B f.
  induction l as [| h t IH].
  - intros x P.
    simpl. simpl in P.
    apply P.
  - intros x H.
    simpl.
    simpl in H. destruct H as [Hxh | Hxt].
    + left. f_equal. apply Hxh.
    + right. specialize IH with (x := x).
      apply IH in Hxt. apply Hxt.
Qed.

Theorem In_map_iff' :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <->
  exists x, f x = y /\ In x l.
Proof.
  intros A B f.
  induction l as [| h t IH].
  - intros y.
    split.
    + intros H. exfalso. simpl in H. apply H.
    + intros [x [H1 H2]]. simpl. simpl in H2. apply H2.
  - intros y.
    split.
    + intros H.
Abort.

(** Why don't need generalize induction Hypothesis here? *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <->
  exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x l' IHl'].
    + intros H. simpl in H. exfalso. apply H.
    + intros H. simpl in H. destruct H as [Hl | Hr].
      ++ exists x. split.
         +++ symmetry. apply Hl.
         +++ simpl. left. reflexivity.
      ++ apply IHl' in Hr as [x0 [H1 H2]]. 
         exists x0. split.
         +++ apply H1.
         +++ simpl. right. apply H2.
  - intros [x [Hl Hr]].
    rewrite <- Hl.
    apply In_map.
    apply Hr.
Qed.

Theorem In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - intros l'' a.
    split.
    + intros H. simpl in H. right. apply H.
    + intros H. simpl. destruct H as [Hl | Hr].
      ++ simpl in Hl. exfalso. apply Hl.
      ++ apply Hr.
  - split.
      + intros H.
        simpl in H. simpl. destruct H as [H1 | H2].
        ++ left. left. apply H1.
        ++ specialize IH with (l' := l'0).
           specialize IH with (a := a).
           destruct IH as [IHl IHr].
           apply IHl in H2. destruct H2 as [H2l | H2r].
           +++ left. right. apply H2l.
           +++ right. apply H2r.
      + intros H.
        simpl. simpl in H. 
        specialize IH with (l' := l'0).
        specialize IH with (a := a).
        destruct IH as [IHl IHr].
        apply or_assoc in H. destruct H as [Hl | Hr].
        ++ left. apply Hl.
        ++ apply IHr in Hr. right. apply Hr.
Qed.

(** P n := Property P holds of n. *)

(** Don't know how to express property of some elements not hold.
   I don't know what does this P mean.
   Okay I know, we can use True and False to represent a proposition is correct or not.*)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [ ] => True
  | h :: t => P h /\ All P t
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  induction l as [| h l' IHl'].
  - split.
    + intros H1. reflexivity.
    + intros H2 x H3. simpl in H3. exfalso. apply H3.
  - split.
    + intros H1. simpl. split.
      ++ specialize H1 with (x := h).
         apply H1. simpl. left. reflexivity.
      ++ apply IHl'. intros x H2. apply H1. simpl. right. apply H2.
    + intros H1 x H2. simpl in H1. destruct H1 as [H1a H1b]. destruct IHl' as [IHl'1 IHl'2].
Abort.

(** I think I state the problem correct. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if odd n then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
  (odd n = true -> Podd n) ->
  (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  induction n as [| n' IHn'].
  - unfold combine_odd_even. simpl. apply H2. unfold odd. reflexivity. - unfold combine_odd_even. 
Abort.
(** Don't know how to simplify if else expression. *)

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n H1 H2.
  induction n as [| n' IHn'].
  - unfold combine_odd_even in H1. rewrite -> H2 in H1. apply H1.
  - unfold combine_odd_even in H1. rewrite -> H2 in H1. apply H1.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n H1 H2.
  induction n as [| n' IHn'].
  - unfold combine_odd_even in H1.
    rewrite -> H2 in H1.
    apply H1.
  - unfold combine_odd_even in H1.
    rewrite -> H2 in H1.
    apply H1.
Qed.

(** ** Applying Theorem to Arguments ** **)
(** Rocq treats proofs as first-class objects.
   Podd : nat -> Prop is a property which a natural number might hold. *)

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

Check @rev.
(** if we leave off the colon and type, Check will print theses types. 

   add_comm refers to proof object. 

   logical derivation establishing the truth of the statement.

   To apply a theorem, one only need to match the type. *)

(** Is it currying? *)
Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (add_comm x (y + z)).
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** Use theorem as a function.
   Of course we can use our little currying technics. 

   Wildcard _ can also be used in theorem application. *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l Hxl.
  unfold not.
  intros Hl.
  rewrite -> Hl in Hxl.
  simpl in Hxl.
  apply Hxl.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(**
  in_not_nil : A (x : A) (l : list A), P -> Q *)

(** ** Working with Decidable Properties ** **)

(** Difference between bool and Prop

   Every Rocq expression of type bool can be simplified in a finite number of steps to either true of false.

   A function of type nat -> bool must be a function takes a nat and yield either true or false in finite time.

   Prop includes both decidable and undecidable mathematical propositions.

   Why propositional equality can do rewrite?

   We have two ways to formalize a property:
   1. As a boolean computation : even 42 = true
   2. As a function into Prop : Even 42
*)

(** boolean computation is the same as the function way *)
Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k.
  simpl.
  induction k as [| k' Ih].
  + reflexivity.
  + rewrite <- Ih.
    reflexivity.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n.
  induction n as [| n'].
  - exists 0. reflexivity.
  - rewrite -> (even_S n'). destruct IHn'.
    destruct (even n') eqn:E.
    + simpl. exists x. rewrite <- H. reflexivity.
    + simpl. rewrite -> H. exists (S x). reflexivity.
Qed.

(** For different cases can use different value. Make the statement general is really important. *)

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n.
  unfold iff.
  split.
  - intros H.
    destruct (even_double_conv n) as [k Hk].
    rewrite -> Hk.
    unfold Even.
    exists k.
    rewrite -> H.
    reflexivity.
  - intros [k Hk].
    rewrite -> Hk.
    apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2.
  unfold iff.
  split.
  - apply eqb_true.
  - intros H. rewrite -> H. apply eqb_refl.
Qed.

(** Proposition way or boolean way?

   - Booleans are more useful for defining functions.

   Props can't be test true or false.
  *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.
(* "n = 2" has type Prop *)

(** For program extraction's usage, in Rocq's core language it is designed so that every function if can express is computable and total. *)

(** Computable & Total **)

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

(** Express in Prop is much easier but stating facts using booleans is enabling some proof automation - Proof by reflection *)

(** Prop **)
Example even_1000 : Even 1000.
Proof.
  unfold Even.
  exists 500.
  reflexivity.
Qed.

(** Boolean **)
Example even_1000' : even 1000 = true.
Proof.
  reflexivity.
Qed.

(** How do we define = in Rocq? **)

(**

Inductive eq {A : Type} (x : A) : A -> Prop :=
  | eq_refl : eq x x.

Notation "x = y" := (eq x y) : type_scope.

= is propositional equality in Rocq

Definition equality is being realize inside Rocq's kernel, it can't be build or being proved.
*)

(** negation of boolean is staightforward to prove. *)
Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

(** proposition negation can be difficult to work with. We have the trade-off here. *)
Example not_even_1001'' : not (Even 1001).
Proof.
  unfold not.
  intros H.
  unfold Even in H.
  (* We need indution on the hypothesis and then prove that all the cases lead to contradiction. *)
Abort.

(** We can prove this by changing propositions to booleans. **)

Example not_even_1001' : not (Even 1001).
Proof.
  Check even_bool_prop.
  Check (even_bool_prop 1001).
  intros H.
  rewrite <- even_bool_prop in H.
  (* I can't understand why I need to intro first, then rewrite. *)
  simpl in H.
  discriminate H.
  Qed.

(** Generally, knowing (n =? m) = true is of little help in the middle of a proof involving n and m. **)

  Lemma plus_eqb_example : forall n m p : nat, n =? m = true -> n + p =? m + p = true.
  Proof.
    intros n m p H.
    rewrite eqb_eq in H.
    rewrite -> H.
    rewrite eqb_eq.
    reflexivity.
  Qed.

(** One of the main tricks here is to transfer between the boolean world and the proposition world. **)

Theorem andb_true_iff : forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  unfold iff.
  split.
  - intros H. unfold andb in H.
    split.
    + destruct b1 eqn:E.
      ++ reflexivity.
      ++ discriminate H.
    + destruct b1 eqn:E.
      ++ apply H.
      ++ discriminate H.
  - intros H.
    destruct H as [H1 H2].
    unfold andb.
    rewrite -> H1. apply H2.
Qed.

(* Markdown environment *)
(** *)

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* Destruct booleans will make it easier. *)
  intros b1 b2.
  destruct b1, b2.
  - split.
    + intros H. left. reflexivity.
    + intros H. unfold orb. reflexivity.
  - split.
    + intros H. simpl in H. left. reflexivity.
    + intros H. simpl. reflexivity.
  - split.
    + intros H.
      right. reflexivity.
    + intros H. simpl. reflexivity.
  - split.
    + intros H. simpl in H. discriminate H.
    + intros H. destruct H. discriminate. discriminate.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  split.
  - intros H.
    rewrite <- not_true_iff_false in H.
    unfold not.
    intros Heq.
    apply H.
    rewrite <- Heq.
    Search "=?".
    apply eqb_refl.
  - unfold not.
    intros H.
    Search "=?".
    destruct (x =? y) eqn:E.
    + Search "=?".
      apply eqb_true in E.
      apply H in E.
      contradiction.
    + reflexivity.
Qed.

(** 这里用到了一些小技巧：
   1. Search 的使用
   2. 对 pattern 进行 destruct *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1 with
  | nil => match l2 with
           | nil => true
           | h :: t => false
           end
  | h1 :: t1 => match l2 with
                | nil => false
                | h2 :: t2 => if eqb h1 h2 then eqb_list eqb t1 t2 else eqb h1 h2
                end
  end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
  (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) -> forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb Ha l1 l2.
  split.
  (* eqb_list eqb l1 l2 = true -> l1 = l2 *)
  - intros Hl.
    destruct l1 eqn:E1.
    + simpl in Hl.
      destruct l2.
      ++ reflexivity.
      ++ discriminate Hl.
    + simpl in Hl.
      destruct l2 eqn:E2.
      ++ discriminate Hl.
      ++ specialize Ha with (a1 := x).
         specialize Ha with (a2 := x0).
         destruct (eqb x x0) eqn:Eeqb.
  (* l1 = l2 -> eqb_list eqb l1 l2 = true *)
Abort.

(** Feel like on the wrong way. But I think I'm doing the definition right. *)

(** 
   ## The Logic of Rocq
   Rocq's logical core is the Calculus of Inductive Constructions.

   ### Functional Extensionality

   Equality in Rocq is polymorphic.
 *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof.
  reflexivity.
Qed.

(** forall x, f x = g x -> f = g is so-called function extensionality. 

   extensionality is the property pertains with the object's observable behavior. 

   extensionality is not build-in for Rocq. *)

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y}, (forall (x : X), f x = g x) -> f = g.

(** Axiom = Theorem with admitted. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(* Print Assumptions help us to check if a proof relies on any additional axioms. *)
Print Assumptions function_equality_ex2.

(** #### Tail-recursive for list-reversing *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

(* Tail-recursive just means recursive call is the last operation. *)

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma rev_append_app : forall X (l1 l2 : list X), rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X l1.
  induction l1 as [| h t IH].
  - intros l2. reflexivity.
  - induction l2 as [| h2 t2 IH2].
    + Search "[ ]".
      rewrite -> app_nil_r.
      reflexivity.
    + specialize IH with (l2 := h :: h2 :: t2).
      simpl. rewrite -> IH.
Admitted.

(** 我就是把原命题换了一个形式来做了一遍而已 *)


Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intro l.
  (* induction l as [|h t IHt] eqn:E. *)
  (* If I need eqn:E, then the weird thing also happens. *)
  induction l as [| h t IHt].
  - unfold tr_rev. reflexivity.
    (* l = h :: t*)
  - unfold tr_rev in IHt. unfold tr_rev. simpl. rewrite <- IHt.
    (* what does l = t here mean? this means if l is a shorter list. *)
    + (* need a stronger version lemma. *)
      apply rev_append_app.
Qed.

(** #### Classical vs. Constructive Logic *)

Definition excluded_middle := forall P : Prop, P \/ ~ P.

(* excluded_middle can't be derived in Rocq.

   To prove P \/ ~ P, we need to prove one of the P or ~ P.

   But forall P is an arbitrary proposition which we know nothing about. *)

Theorem restricted_excluded_middle : forall P b, (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite -> H. reflexivity.
  - right. unfold not. intros Hp. rewrite -> H in Hp. discriminate.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  (* P := n = m *)
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** Advantage of not assuming excluded middle:

   Can make stronger claims, i.e. every proof of existence is constructive.

   Logics like Rocq's, which don't assume the excluded middle, are referred to as constructive logics. 

   Logical systems such as ZFC, are referred to as classical.

   I feel like constructive means, in exists b, P b, we must give a b. 

   Contradiction need excluded middle, to show contradiction is the same to show we can freely move double negation. *)

Theorem excluded_middle_irrefutable : forall (P : Prop), ~ ~ (P \/ ~ P).
Proof.
  intros P.
  unfold not.
  intros H. 
  apply H.
  right. intros HP. apply H. left. apply HP.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
  ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros H X P Hx a.
  unfold excluded_middle in H.
  specialize (H (P a)).
  destruct H as [H' | H'N].
  - apply H'.
  - exfalso.
    apply Hx.
    exists a.
    apply H'N.
Qed.

