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
    match s with 
    | nil => nil
    | h :: t => if h =? v then t else h :: (remove_one v t)
    end.

  Example test_remove_one1:
      count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed. 
 
  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed. 
  
  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. reflexivity. Qed. 

  Theorem add_inc_count : forall n : nat, forall b : bag, length (add n b) = length b + 1.
  Proof.
    intros n b.
    simpl.
    rewrite -> S_add_1_r.     
    reflexivity.
  Qed.

  (* ** Reasoning about Lists ** *)
  Theorem nil_app : forall l : natlist,
    [] ++ l = l.
  Proof. reflexivity. Qed.

  Theorem tl_length_pred : forall l : natlist,
    pred (length l) = length (tl l).
  Proof.
    intros l. destruct l as [| n l'].
    - (* l = nil *)
      reflexivity.
    - (* l = h :: t *)
      reflexivity.
  Qed.
  
  (** Reading proof scripts will not help you very much.
      Rather, it is important to step through the details of each one using Rocq and think about what each step achieves.
      Otherwise it is more or less guaranteed that the exercises will make no sense when you get to them. 'Nuff said.*)

  (* ** Induction on Lists ** *)
  (** Induction is the most common technique to prove things about lists.
      Each inductive declaration defines a set of data values that can and only can be built up using the declared constructors.

      Induction on lists:
     - Show that P is true of l when l is nil
     - Then show that P is true of l when l is cons n l' for some number n and some smaller list l', assuming that P is true for l'.*)

  Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
  Qed.

  (** Proof in human way will include more explicit signposts.*)

  (* ** Generalizing Statements ** *)
  (** One can generalizing statements cause it is easier to prove by induction.*)
  
  Theorem repeat_double_firsttry : forall c n : nat,
    repeat n c ++ repeat n c = repeat n (c + c).
  Proof.
    intros c n. induction n as [| n' IHn'].
    - induction c as [| c' IHc'].
      -- reflexivity.
      -- simpl.
  Abort.
  (* Just couldn't prove it! *)

  Theorem repeat_plus : forall c1 c2 n : nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
  Proof.
    intros c1 c2 n.
    induction c1 as [| c1' IHc1'].
    - simpl. reflexivity.
    - simpl. rewrite <- IHc1'. reflexivity.
  Qed.

  (* ** Reversing a list ** *)
  Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.

  Example test_rev1 : rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.

  Example test_rev2 : rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem rev_length_firsttry : forall l : natlist,
    length (rev l) = length l.
  Proof.
    intros l. induction l as [| n l' IHl'].
    - (* l = nil *)
      reflexivity.
    - simpl.
      (* We don't have useful equation to simplify ++. *)
      rewrite <- IHl'.
  Abort.
  
  (** One should notice that the reverse list is just a list, so if we can generalize this lemma to all the natlist then it will work for reverse list.*)

  Theorem app_length_S : forall l n,
    length (l ++ [n]) = S (length l).
  Proof.
    intros l n. induction l as [| h l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem rev_length_firsttry : forall l : natlist,
    length (rev l) = length l.
  Proof.
    intros l. induction l as [| n l' IHl'].
    - (* l = nil *)
      reflexivity.
    - simpl. rewrite -> app_length_S. rewrite -> IHl'. reflexivity.
  Qed.
  
  (** Of course we can do a more general version.*)
  
  Theorem app_length_inductionl1try : forall l1 l2 : natlist,
    length (l1 ++ l2) = length l1 + length l2.
  Proof.
    intros l1 l2. induction l2 as [| n l2' IHl2'].
    - induction l1 as [| m l1' IHl1'].
      (* Need induction here cause ++ is defined to add elements in l1 before elements in l2. Thus induction on l2 make no usage. *)
      -- reflexivity.
      -- simpl. rewrite -> IHl1'. reflexivity.
    - induction l1 as [| m l1' IHl1'].
      -- reflexivity.
      -- simpl. rewrite -> IHl1'.
         --- reflexivity.
  Abort. 

  Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = length l1 + length l2.
  Proof.
    intros l1 l2. induction l1 as [| n l1 IHl1'].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
  Qed.
  
  (* ** Search ** *)
  (** It's hard to remember the name of a theorem.*)
  Search rev.
  (* Rocq will display all the name contaions rev. *)
  Search (_ + _ = _ + _). 
  (* One can also use pattern to search. *)
  Search (_ + _ = _ + _) inside ProofByInduction.
  (* One can also restrict the module of the search result. *)
  Search (?x + ?y = ?y + ?x).
  (* The question mark is to indicate that it is a variable in the search pattern. *)

  Theorem app_nil_r : forall l : natlist,
    l ++ [] = l.
  Proof.
    intros l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem rev_app_distr : forall l1 l2 : natlist,
    rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros l1 l2. induction l1 as [| n l1' IHl1'].
    - simpl. rewrite -> app_nil_r. reflexivity.
    - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
    rev (rev l) = l.
  Proof.
    induction l as [| n l1' IHl1'].
    - reflexivity.
    - simpl. rewrite -> rev_app_distr. rewrite -> IHl1'. reflexivity.
  Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite app_assoc. rewrite app_assoc. reflexivity.
  Qed.

  Lemma nonzeors_app : forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2. induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl. induction n as [| n' IHn'].
      -- rewrite IHl1'. reflexivity.
      -- simpl.rewrite IHl1'. reflexivity.
  Qed.

  Fixpoint eqblist (l1 l2 : natlist) :=
    match l1 with
    | nil => match l2 with
             | nil => true
             | h :: t => false
             end
    | h :: t => match l2 with
                | nil => false
                | n :: m => if h =? n then eqblist t m else false
                end
    end.

  Compute (eqblist [1;2;3] [1;2;3]).
  Compute (eqblist [1;2;3] [1;2;4]).

  Theorem eqblist_refl : forall l : natlist,
    true = eqblist l l.
  Proof. 
    intros l. induction l as [| h l' IHl'].
    - reflexivity.
    - simpl. rewrite <- IHl'.
      induction h as [| h' IHh'].
      -- reflexivity.
      -- simpl. rewrite <- IHh'. reflexivity.
  Qed.
  
  Theorem count_member_nonzero : forall (s : bag),
    1 <=? (count 1 (1 :: s)) = true.
  Proof.
    intros s. induction s as [| h s' IHs'].
    - reflexivity.
    - simpl. reflexivity.
  Qed.

  Theorem leb_n_Sn : forall n,
    n <=? (S n) = true.
  Proof.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
  Qed.
  
  Theorem remove_does_not_increase_count : forall (s : bag),
    (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
  Proof.
    induction s as [| h s' IHs'].
    - reflexivity.
    - simpl. induction h as [| h' IHh'].
      -- simpl. rewrite leb_n_Sn. reflexivity.
      -- simpl. rewrite IHs'. reflexivity.
  Qed.

  Theorem bag_count_sum : forall (s1 s2 : bag), forall n : nat,
    (count n s1) + (count n s2) = count n (sum s1 s2).
  (* count n is s1 and s2 separately is the same as count in s1 + s2. *)
  Proof.
    intros s1 s2 n. induction s1 as [| h s1' IHs1'].
    - reflexivity.
    - simpl. destruct (h =? n).
      -- simpl. rewrite -> IHs1'. reflexivity.
      -- rewrite IHs1'. reflexivity.
  Qed.

  (* destruct can work on the expressions! *)
  (* destruct is like case by case. *)

  Theorem incolution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
  Proof.
    intros f H1 n1 n2 E1.
    rewrite -> H1. rewrite <- E1. rewrite <- H1. reflexivity.
  Qed.

  Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 E1.
    rewrite <- rev_involutive. rewrite <- E1. rewrite -> rev_involutive. reflexivity.
  Qed.

  (** * Options *)
