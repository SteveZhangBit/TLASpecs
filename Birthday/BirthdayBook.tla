---------------------------- MODULE BirthdayBook ----------------------------
(***************************************************************************)
(* Name is the set of names.  Date is the set of dates.  None is a special *)
(* value for null data.                                                    *)
(***************************************************************************)
CONSTANT Name, Date, None

VARIABLES known,    \* The set of all the known names in the birthday book.
          birthday  \* A function from Name to Date representing the birthday
                    \* of a name in the birthday book.

TypeInvariant == /\ known \subseteq Name
                 /\ birthday \in [Name -> Date \cup {None}]

StateInvariant ==
  (*************************************************************************)
  (* It asserts that the names in function "birthday" which is not mapped  *)
  (* to None should be equal to the set "known".                           *)
  (*************************************************************************)
  LET names == {name \in Name : birthday[name] /= None}
  IN  known = names

AddBirthday(name, date) ==
  (*************************************************************************)
  (* Add a name and its birthday to the birthday book.  The name should    *)
  (* not be in the birthday book.                                          *)
  (*************************************************************************)
  /\ name \notin known
  /\ known' = known \cup {name}
  /\ birthday' = [birthday EXCEPT ![name] = date]

Init == /\ known = {}
        /\ birthday = [name \in Name |-> None]

Next == \E name \in Name : \E date \in Date : AddBirthday(name, date)

Spec == Init /\ [][Next]_<<known, birthday>>

THEOREM Spec => [](TypeInvariant /\ StateInvariant)
=============================================================================
\* Modification History
\* Last modified Mon Mar 26 19:55:42 EDT 2018 by changjian
\* Created Sun Feb 25 21:07:01 EST 2018 by changjian
