(* * Exercise : nandb * *)

Inductive bool : Type :=
  | true
  | false.

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  if b1 then
    if b2 then false
    else true
  else true.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* * Exercise : andb3 * *)

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) :=
  if b1 then 
    if b2 then b3
    else false
  else false.

Example test_andb31: (andb3 true true true) = true.

Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* * Exercise : factorial * *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => S 0
  | S n' => mult n (factorial n')
  end.

Compute (factorial 4).

Example test_factorial1 : (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2 : (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

