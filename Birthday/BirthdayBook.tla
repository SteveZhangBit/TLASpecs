---------------------------- MODULE BirthdayBook ----------------------------
CONSTANT Name, Date, None

VARIABLES known, birthday

TypeInvariant == /\ known \subseteq Name
                 /\ birthday \in [Name -> Date \cup {None}]

StateInvariant == LET names == {name \in Name : birthday[name] /= None}
                  IN  known = names

AddBirthday(name, date) == /\ name \notin known
                           /\ known' = known \cup {name}
                           /\ birthday' = [birthday EXCEPT ![name] = date]

Init == /\ known = {}
        /\ birthday = [name \in Name |-> None]

Next == \E name \in Name : \E date \in Date : AddBirthday(name, date)

Spec == Init /\ [][Next]_<<known, birthday>>

THEOREM Spec => [](TypeInvariant /\ StateInvariant)
=============================================================================
\* Modification History
\* Last modified Sun Mar 25 16:11:24 EDT 2018 by changjian
\* Created Sun Feb 25 21:07:01 EST 2018 by changjian
