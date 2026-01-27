From LogicalFoundations Require Export ProofByInduction.
Module NatList.

  (* ** Pairs of Numbers ** *)
  (** In Inductive type definition, each constructor can take any number of arguments.*)
  Inductive natprod : Type :=
    | pair (n1 n2 : nat).
  (* The one and only way to contruct a pair of numbers is by applying the constructor pair to two arguments of type nat. *)

  Check (pair 3 5) : natprod.

  (** Functions for extracting the first and second components of a pair.*)

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Compute (fst (pair 3 5)).

  Notation "( x , y )" := (pair x y).

  Definition fst' (p : natprod) : nat :=
    match p with
    | (x,y) => x
    end.

  Definition snd' (p : natprod) : nat :=
    match p with
    | (x,y) => y
    end.
  
  Compute (fst' (pair 3 5)).
  (* Notation and the original one are the same thing! *)

  Theorem fst_fst'_same : forall p : natprod, fst' p = fst p.
  Proof.
    intro p.
    reflexivity.
  Qed.

  Theorem Notation_same : forall x y : nat, pair x y = (x,y).

  Proof.
    intros x y.
    reflexivity.
  Qed.

  (** Can't match a pair with multiple patterns.

    Cause althrough in pair n m it has two arguments one can manipulate on, there's only one pattern!*)

  (** We need to expose the structure of p so that simpl cna perform the pattern match in fst and snd.*)

  Theorem surjective_pairing : forall (p : natprod), p = (fst p, snd p).

  Proof.
    intro p.
    destruct p as [fstp sndp].
    (* since only one constructor so we only have one branch with two arguments.*)
    - reflexivity.
  Qed.
  
  (** natprod have only one constructor, so we say it can only be constructed in one way.*)

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x,y) => (y,x)
    end.

  Theorem snd_fst_is_swap : forall (p : natprod), (snd p, fst p) = swap_pair p.
  Proof.
    intro p.
    destruct p as [n m].
    simpl.
    reflexivity.
  Qed.

  Definition fst_swap_is_snd : forall (p : natprod), fst (swap_pair p) = snd p.
  Proof.
    intro p.
    destruct p as [n m].
    simpl.
    reflexivity.
  Qed.

  (* ** List of Numbers ** *)



