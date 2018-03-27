-------------------------- MODULE BirthdayBookArr --------------------------
EXTENDS Naturals, Sequences

(***************************************************************************)
(* Name is the set of names.  Date is the set of dates.  None is a special *)
(* value for null data.                                                    *)
(***************************************************************************)
CONSTANT Name, Date, None

VARIABLES names,  \* A sequence of all the names in the birthday book.
          dates,  \* A sequence of all the dates in the birthday book. The
                  \* date at index i is the birthday for the name at index i
                  \* in names.
          size    \* The total size of the birthday book.

TypeInvariant == /\ names \in Seq(Name)
                 /\ dates \in Seq(Date)
                 /\ size \in Nat

StateInvariant ==
  (*************************************************************************)
  (* There should be have identical names in the birthday book.            *)
  (*************************************************************************)
  /\ \A i, j \in 1 .. size : i /= j => names[i] /= names[j]
  /\ Len(names) = size
  /\ Len(dates) = size

Init == /\ names = <<>>
        /\ dates = <<>>
        /\ size = 0

AddBirthday(name, date) ==
  (*************************************************************************)
  (* Add a name and its birthday to the birthday book.  To ensure the name *)
  (* is not already in the birthday book, it compares the input name with  *)
  (* all the existing names.                                               *)
  (*************************************************************************)
  /\ \A i \in 1 .. size : name /= names[i]
  /\ size' = size + 1
  /\ names' = Append(names, name)
  /\ dates' = Append(dates, date)

Next == \E name \in Name : \E date \in Date : AddBirthday(name, date)

Spec == Init /\ [][Next]_<<names, dates, size>>

THEOREM Spec => [](TypeInvariant /\ StateInvariant)

----------------------------------------------------------------------------

(***************************************************************************)
(* Get all the names in the sequence "names".  This should be mapped to    *)
(* the "known" variable in Module BirthdayBook.                            *)
(***************************************************************************)
LOCAL Known == {names[i] : i \in 1..size}

(***************************************************************************)
(* A helper functino to get the index of a given name in the "names"       *)
(* sequence.                                                               *)
(***************************************************************************)
LOCAL FindDate(name) == CHOOSE i \in 1..size : names[i] = name

(***************************************************************************)
(* Since birthday is a total function from Name to Date, if the name is in *)
(* the "Known" set, then map it to its corresponding date in "dates";      *)
(* otherwise, map it to None.                                              *)
(***************************************************************************)
BirthdayBook == INSTANCE BirthdayBook
                WITH     known <- Known,
                         birthday <- [name \in Name |->
                                        IF name \in Known THEN
                                          dates[FindDate(name)]
                                        ELSE
                                          None]

THEOREM Spec => BirthdayBook!Spec

(***************************************************************************)
(* The implementation should satisfy the invariants in the abstract model. *)
(***************************************************************************)
BirthdayBookInv == [](/\ BirthdayBook!TypeInvariant
                      /\ BirthdayBook!StateInvariant)
THEOREM Spec => BirthdayBookInv

=============================================================================
\* Modification History
\* Last modified Mon Mar 26 20:10:52 EDT 2018 by changjian
\* Created Sun Feb 25 21:24:14 EST 2018 by changjian
