Set Warnings "-notation-overridden".
From LogicalFoundations Require Export Logic.

(** ## Inductively Defined Propositions *)

(** Collatz Conjecture *)

Fixpoint div2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

(** If the sequence starting from any number by the csf will eventually reach 1? 

   We try to define a recursive function that calculates the total number of steps that it takes for such a sequence to reach 1. *)

Fail Fixpoint reaches1_in (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + reaches1_in (csf n).

(** Rocq will reject, cause it need to make sure that every such function need to converge. 

   Functions in Rocq are required to be total.

   Defined as an recursively defined property of numbers. *)

Fail Fixpoint Collatz_holds_for (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
      else Collatz_holds_for ((3 * n) + 1)
  end.

(** div2 n can be strictly smaller, but (3 * n + 1) isn't. 

   I deeply feel like the traditional way is for someone who can going deeper! But the way we defined it to be a set of rules is a bottom-up way! 

   Three rules for n to become a collatz number:
   1. 1 is collatz number
   2. even n and n/2 is a collatz number then n is a collatz number
   3. odd n and 3 * n + 1 is a collatz number then n is a collatz number. *)

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true ->
      Collatz_holds_for (div2 n) ->
      Collatz_holds_for n
  | Chf_odd (n : nat) : even n = false ->
      Collatz_holds_for ((3 * n) + 1) ->
      Collatz_holds_for n.

(** With those rules we can build proof on if some number is a collatz number. *)

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

(* Collatz conjecture *)
Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.

(** ### Binary relation for comparing numbers 

   Binary relation has type : X -> X -> Prop *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

(** ### Transitive Closure

   The transitive closure of a relation R is the smallest relation that contains R and that is reflexive and transitive. 

   We can observe few facts:
   1. R x y holds implies clos_trans R x y holds
   2. clos_trans R is transitive. *)

Inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y -> clos_trans R y z -> clos_trans R x z.
(** It might take some effort to show that this is the smallest, but if we have another clos_trans' R, by definition clos_trans R should belongs to it. *)

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  | po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss.

(** Parent of is not transitive.

   Sage is the parent of Cleo,
   Cleo is the parent of Moss,
   Sage is not the parent of Moss. *)

Theorem parent_not_transitive : ~ parent_of Sage Moss.
Proof.
Abort.
(** We don't have enought info. to prove it. We defined the transitive closure. *)

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of.
  apply t_trans with (y := Cleo).
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM.
Qed.

(** #### Reflexive and Transitive Closure 

   Reflexive and Transitive Closure is the smallest relation that contains R and that is reflexive and transitive. *)

Inductive clos_refl_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | rt_step (x y : X) :
      R x y -> clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

(** Compatible with Collatz step function. *)

(* R := eq (csf n) m *)

Definition cs (n m : nat) : Prop := csf n = m.

Definition cms n m := clos_refl_trans cs n m.

Conjecture collatz' : forall n, n <> 0 -> cms n 1.

(** It feels like Collatz conjecture and a reflexive and transitive relation just fit each other. *)

Inductive clos_symm_refl_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | srt_step (x y : X) :
      R x y -> clos_symm_refl_trans R x y
  | srt_refl (x : X) :
      clos_symm_refl_trans R x x
  | srt_trans (x y z : X) :
      clos_symm_refl_trans R x y ->
      clos_symm_refl_trans R y z ->
      clos_symm_refl_trans R x z
  | srt_symm (x y : X) :
      clos_symm_refl_trans R x y -> clos_symm_refl_trans R y x.

(** They are just rules we can play with, when one think of the proof process. *)

(** #### Permutations

   The beauty of type theory lies in the way we can express so proposition into a set of inductive rules. 

   Permutation is a set of rules where:
   1. One can swap [a; b; c] [a; c; b]
   2. One can swap [a; b; c] [b; a; c]
   3. Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3 *)

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Example Is_123_Perm : Perm3 [1;2;3] [1;2;3].
Proof.
  apply perm3_trans with [2;1;3].
  apply perm3_swap12.
  apply perm3_swap12.
Qed.

(** #### Evenness 

   Two ways of stating a proposition is even:
   1. even n = true;
   2. exists k, n = double k. 

   We can also establish the evenness form two rules:
   1. ev 0
   2. ev n -> ev (S (S n)) *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** Each number can be even according to a separate constructor.

   Difference between inductively defined datatypes and inductively defined definition.

   Here ev : nat -> Prop
   In stead of a function ev (n : nat) : Prop 

   index or annotation:
   : nat 

   parameter:
   nat : 

   It's like defining a Rocq property together with two "evidence constructors" *)

Module EvPlayground.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).

End EvPlayground.

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n Hn.
  apply ev_SS.
  apply ev_SS.
  apply Hn.
Qed.

Theorem ev_double : forall n, ev (double n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* ev (double 0) *)
    simpl. apply ev_0.
  - (* ev (double (S n')) *)
    simpl. apply ev_SS. apply IHn'.
Qed.

(** #### Constructing Evidence for Permutations *)

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2 := [1; 3; 2]).
  - apply perm3_swap23.
  - apply perm3_trans with (l2 := [3; 1; 2]).
    ++ apply perm3_swap12.
    ++ apply perm3_swap23.
Qed.

(* use place holder _ *)
Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [1;3;2] _ (perm3_swap23 _ _ _) (perm3_trans _ [3;1;2] _ (perm3_swap12 _ _ _) (perm3_swap23 _ _ _))).
Qed.

(** Use () to represent hierachy, we get an informal decision tree! *)

Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply (perm3_trans _ [3;2;1] _ (Perm3_rev') (perm3_swap12 _ _ _)).
Qed.

Lemma Perm3_refl : forall (X : Type) (a b c : X), Perm3 [a;b;c] [a;b;c].
Proof.
  intros X a b c.
  apply (perm3_trans _ [b;a;c] _ (perm3_swap12 _ _ _) (perm3_swap12 _ _ _)).
Qed.

(** ## Using Evidence in Proofs

   If someone gives us evidence E for the proposition ev n, then we know that E must be one of two things:
   1. E = ev_0 and n = 0, or
   2. E = ev_SS n' E' and n = S (S n'), where E' is evidence for n'.

   ### Destructing and Inverting Evidence

   We want to analyze the evidence for (ev n) directly. *)

Lemma ev_inversion : forall (n : nat),
  ev n ->
  (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 : ev_0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split.
    + reflexivity.
    + apply E'.
Qed.

(* We can handle this just like we handle the datatypes, nothing is different here. *)

(** Facts like this are often called "inversion lemmas". *)

Lemma le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros n m H.
  destruct H as [| n' N' HN'] eqn:EH.
  - (* n <= n *)
    left. reflexivity.
  - (* n' <= S H' *)
    right. exists N'. split.
    + reflexivity.
    + apply HN'.
Qed.

(** Inversion lemma can help us to structure proofs. *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H.
  apply ev_inversion in H. destruct H as [H0 | H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnn' H']]. injection Hnn' as Hnn'. rewrite -> Hnn'. apply H'.
Qed.

(** Rocq has inversion tactic for us to do this job. *)

