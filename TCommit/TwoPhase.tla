------------------------------ MODULE TwoPhase ------------------------------
CONSTANT RM

VARIABLES rmState, tmState, tmPrepared, msgs

Messages ==
  (*************************************************************************)
  (* The set os all possible messages.  From RM to TM, each rm will send a *)
  (* "Prepared" message to tm.  From TM to RM, tm will send "Commit" or    *)
  (* "Abort" message to all the rms.                                       *)
  (*************************************************************************)
  [type : {"Prepared"}, rm : RM] \union [type : {"Commit", "Abort"}]

TPTypeInvariant ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "done"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages  \* All messages ever sent, so there is no need
                              \* to remove any message from the set.

TPInit ==
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

TMRcvPrepared(r) ==
  (*************************************************************************)
  (* Describes the receipt of a "Prepared" message from RM r by TM.        *)
  (*************************************************************************)
  /\ tmState = "init"
  (*************************************************************************)
  (* msgs is the set of all messages ever sent.  Thus, the precondition    *)
  (* of the receipt of any message should be the message is already in the *)
  (* msgs set.                                                             *)
  (*************************************************************************)
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \union {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  (*************************************************************************)
  (* Allows steps where the TM sends Commit messages to the RMs and sets   *)
  (* tmState to "done".                                                    *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "done"
  /\ msgs' = msgs \union {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  (*************************************************************************)
  (*   The TM sends Abort messages to the RMs and sets tmState to "done".  *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "done"
  /\ msgs' = msgs \union {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(r) ==
  (*************************************************************************)
  (* RM r sets its state to "prepared" and sends a Prepared message to the *)
  (* TM.                                                                   *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(r) ==
  (*************************************************************************)
  (* When in its "working" state, RM r can go to "aborted" state.          *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(r) ==
  (*************************************************************************)
  (* RM r receives a "commit" message and set its state to "committed"     *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(r) ==
  (*************************************************************************)
  (* RM r receives a "abort" message and set its state to "aborted"        *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
  \/ TMCommit
  \/ TMAbort
  \/ \E r \in RM :
    \/ TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
    \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)

INSTANCE TCommit

=============================================================================
\* Modification History
\* Last modified Thu Jan 04 21:15:27 CST 2018 by changjian
\* Created Wed Jan 03 21:20:19 CST 2018 by changjian
