-------------------------- MODULE BirthdayBookArr --------------------------
EXTENDS Naturals, Sequences

CONSTANT Name, Date, None

VARIABLES names, dates, size

TypeInvariant == /\ names \in Seq(Name)
                 /\ dates \in Seq(Date)
                 /\ size \in Nat

StateInvariant == /\ \A i, j \in 1 .. size : i /= j => names[i] /= names[j]
                  /\ Len(names) = size
                  /\ Len(dates) = size

Init == /\ names = <<>>
        /\ dates = <<>>
        /\ size = 0

AddBirthday(name, date) == /\ \A i \in 1 .. size : name /= names[i]
                           /\ size' = size + 1
                           /\ names' = Append(names, name)
                           /\ dates' = Append(dates, date)

Next == \E name \in Name : \E date \in Date : AddBirthday(name, date)

Spec == Init /\ [][Next]_<<names, dates, size>>

THEOREM Spec => [](TypeInvariant /\ StateInvariant)

----------------------------------------------------------------------------

LOCAL Known == {names[i] : i \in 1..size}

LOCAL FindDate(name) == CHOOSE i \in 1..size : names[i] = name

BirthdayBook == INSTANCE BirthdayBook
                WITH     known <- Known,
                         birthday <- [name \in Name |->
                                        IF name \in Known THEN
                                          dates[FindDate(name)]
                                        ELSE
                                          None]

THEOREM Spec => BirthdayBook!Spec
THEOREM Spec => [](BirthdayBook!TypeInvariant /\ BirthdayBook!StateInvariant)

=============================================================================
\* Modification History
\* Last modified Wed Mar 21 23:50:02 EDT 2018 by changjian
\* Created Sun Feb 25 21:24:14 EST 2018 by changjian
