------------------------------ MODULE TCommit ------------------------------
CONSTANT RM

VARIABLE rmState

vars == <<rmState>>

TCTypeInvariant ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCConsistent == \A r1, r2 \in RM : ~ /\ rmState[r1] = "committed"
                                     /\ rmState[r2] = "aborted"

TCInit == rmState = [r \in RM |-> "working"]

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

canCommit == \A r \in RM : rmState[r] = "prepared" \/ rmState[r] = "committed"

notCommitted == \A r \in RM : rmState[r] # "committed"

Decide(r) == \/ /\ rmState[r] = "prepared"
                /\ canCommit
                /\ rmState' = [rmState EXCEPT ![r] = "committed"]
             \/ /\ (rmState[r] = "working" \/ rmState[r] = "prepared")
                /\ notCommitted
                /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

TCSpec == TCInit /\ [][TCNext]_<<rmState>> /\ WF_vars(TCNext)

Termination ==
  <>(\/ rmState = [r \in RM |-> "committed"]
     \/ rmState = [r \in RM |-> "aborted"])

=============================================================================
\* Modification History
\* Last modified Thu Feb 08 16:41:42 EST 2018 by changjian
\* Created Wed Dec 27 08:52:45 CST 2017 by changjian
