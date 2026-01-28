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
  (** List is the generalization of pairs.*)
  Inductive natlist : Type :=
    | nil
    (* empty list *)
    | cons (n : nat) (l : natlist).
    (* recursive definition of list *)

  Definition mylist := cons 1 (cons 2 (cons 3 nil)).

  (* Introduce a convinient notation. *)
  
  Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
  (** What does .. do? *)

  (** All the definition are the same.*)

  Theorem definition_same : [1;2;3] = 1 :: (2 :: (3 :: nil)).
  Proof.
    reflexivity.
  Qed.

  (** Lower the level is the tighter it bounds.*)

  Compute (1 + 2 :: [3]).

  (** It's interesting that list is just nested sets.*)

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | 0 => nil
    | S count' => n :: (repeat n count')
    end.

  Compute repeat 2 10.

  Fixpoint length (l : natlist) : nat :=
    match l with
    | nil => 0
    | h :: t => S (length t)
    end.

  Compute (length (repeat 2 8)).

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).
  Compute [1;2] ++ [3].

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.
  (** tail is a list. *)
  Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.
  
  Example test_hd1 : hd 0 [1;2;3] = 1.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | nil => nil
    | 0 :: t => nonzeros t
    | h :: t => h :: nonzeros t
    end.

  (** A list contains no zeros elements is a list in the following form:
     nonzero :: nozerolist*)

  Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint is_odd (n : nat) : bool :=
    match n with
    | 0 => false
    | S 0 => true
    | S (S n') => is_odd n'
    end.

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | nil => nil
    | n :: t => match is_odd n with
                | false => oddmembers t 
                | true => n :: oddmembers t
                end
    end.

  Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition countoddmembers (l : natlist) : nat := length (oddmembers l).

  Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  Proof.
    reflexivity.
  Qed.

  Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_countoddmembers3:
  countoddmembers nil = 0.
  Proof.
    reflexivity.
  Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h1 :: t1 => match l2 with
                | nil => l1
                | h2 :: t2 => h1 :: h2 :: alternate t1 t2
                  end
    end.

  Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate4:
  alternate [] [20;30] = [20;30].
  Proof.
    reflexivity.
  Qed.

  (** bag is like a set, except each element can appera multiple times rather than once.*)

  Definition bag := natlist.
  
  Fixpoint badcount (v : nat) (s : bag) : nat :=
    match s with
    | nil => 0
    | v :: t => S (badcount v t)
    (* one need notice that here v :: t matches every non-empty list. *)
    end.
 
  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => 0
    | h :: t => if h =? v then S (count v t) else count v t
    end.

  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof.
    reflexivity.
  Qed.

  Definition sum : bag -> bag -> bag :=
    app.
  
  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition add (v : nat) (s : bag) : bag :=
    v :: s.
  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof.
    reflexivity.
  Qed.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Fixpoint member (v : nat) (s : bag) : bool :=
    match s with
    | nil => false
    | h :: t => if v =? h then true else member v t
    end.

  Example test_member1: member 1 [1;4;1] = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_member2: member 2 [1;4;1] = false.
  Proof.
    reflexivity.
  Qed.

  Fixpoint remove_one (v : nat) (s : bag) : bag :=



