--------------------------- MODULE RobustLibrary ---------------------------
EXTENDS Library

INSTANCE Staff

vars == <<books, records, users, staff, out>>

RLibrartNext ==
  \/ LibraryNext
  \/ /\ StaffNext
     /\ UNCHANGED <<books, records, out>>

RLibrarySpec ==
  /\ LibraryInit
  /\ StaffInit
  /\ [][RLibrartNext]_vars

NoUserNoCheckout ==
  (*************************************************************************)
  (* If the library has no user, no book can be checked out.               *)
  (*************************************************************************)
  LET outbooks == {b \in books : records[b].status = "out"}
  IN  [](users = {} => outbooks = {})

THEOREM RLibrarySpec => NoUserNoCheckout

NobodyCantCheckout ==
  (*************************************************************************)
  (* "Nobody" cannot check out any book                                    *)
  (*************************************************************************)
  LET outbooks == {b \in books : /\ records[b].status = "out"
                                 /\ records[b].lastuser = Nobody}
  IN  [](outbooks = {})

THEOREM RLibrarySpec => NobodyCantCheckout

=============================================================================
\* Modification History
\* Last modified Thu Feb 08 10:03:38 EST 2018 by changjian
\* Created Wed Feb 07 17:31:40 EST 2018 by changjian
