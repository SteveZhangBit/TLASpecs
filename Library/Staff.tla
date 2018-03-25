------------------------------- MODULE Staff -------------------------------
CONSTANT RealPerson

VARIABLES
  users,  \* The set of all the users who have regestiered in the library.
  staff   \* The set of all the workers in the library.

StaffTypeInvariant ==
  /\ users \subseteq RealPerson
  /\ staff \subseteq RealPerson

StaffInit ==
  /\ users = {}
  /\ staff = {}

AddStaff(p) ==
  /\ staff' = staff \cup {p}
  /\ UNCHANGED users

RemoveStaff(p) ==
  /\ p \in staff
  /\ staff' = staff \ {p}
  /\ UNCHANGED users

RegisterUser(doer, u) ==
  /\ doer \in staff
  /\ users' = users \cup {u}
  /\ UNCHANGED staff

UnregisterUser(doer, u) ==
  /\ doer \in staff
  /\ u \in users
  /\ users' = users \ {u}
  /\ UNCHANGED staff

StaffNext ==
  \/ \E p \in RealPerson :
        \/ AddStaff(p)
        \/ RemoveStaff(p)
  \/ \E doer \in staff: \E u \in RealPerson :
        \/ RegisterUser(doer, u)
        \/ UnregisterUser(doer, u)

StaffSpec == StaffInit /\ [][StaffNext]_<<users, staff>>
  
=============================================================================
\* Modification History
\* Last modified Thu Feb 08 08:53:01 EST 2018 by changjian
\* Created Wed Feb 07 10:37:39 EST 2018 by changjian
