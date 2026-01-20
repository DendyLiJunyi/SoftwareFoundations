(* * Library files, modules and identifiers * *)

Print Libraries.

Check or_comm.

(** Coq contains files Notations.vo Ltac.vo *)

From Coq Require Bool.Bool.

(** Load all logical and computational content in the file Bool.vo *)

Print Libraries.

(** 

   Now we have two more library. 

   Once a module is being loaded, one can't unrequired it.

*)

Search andb true.

(** Search command search for theorems which has an "andb" keyword. *)

About andb_true_intro.

(** Coq has an internal name to distinguish theorems and lemmas. *)

About andb_prop.

About Bool.andb_true_l.

(** 

Coq.Bool.Bool.andb_true_l is an absolutely qualified identifier / fully qualified identifier.

An absolute qualified identifier consist of the following parts.

   - Coq : logical name of the library.
   - Path of the file containing the identifier in the given library.


Coq accept partially qualified identifier. 

Why not short name?

Silent shadow.

*)

Fail Check andb_true_l.

Locate andb_true_l.
(** 

Locate shows all the constant related to the given name. 

Import a module help us to use a shorter name.

*)

Import Bool.


Check andb_true_l.

Search andb true.
Fail Search andb_true.

(** One can use Fail to make function not working. *)



