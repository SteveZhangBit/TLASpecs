---------------------------- MODULE ClientServer ----------------------------
CONSTANT Client,  \* The set of all the clients.
         Server   \* The set of all the servers.

VARIABLES clientStat, \* A function from a client to its state.
          serverStat, \* A function from a server to its state.
          msgs        \* The set of all the unhandled messages.

CONSTANT NoVal  \* Representing that the server is not processing any data.

vars == <<serverStat, clientStat, msgs>>

Message == [sender : Client] \* A message is a record containing the sender.

ServerStates ==
  (*************************************************************************)
  (* ServerStates defines the record to represent the status of a server.  *)
  (* stat is the current state of the server which could be "Start",       *)
  (* "listening", and "Processing".  When the server starts, it is in the  *)
  (* "Start" state.  Then, after initialization, the server changes to     *)
  (* "Listening" state to process requests.  In the listening state, the   *)
  (* server should accept an unhandled message from the msgs set and then  *)
  (* goes into the "Processing" state to process it.  After processing the *)
  (* message, the server backs to the "Listening" state.                   *)
  (*                                                                       *)
  (* cur stores the current message the server is processing.  If the      *)
  (* server is not processing any value, cur equals NoVal.                 *)
  (*************************************************************************)
  [stat : {"Start", "Listening", "Processing"}, cur : Message \cup {NoVal}]

ClientStates ==
  (*************************************************************************)
  (* The set of all the possible states of the client.  A client first     *)
  (* starts in the "Start" state.  After initialization, it goes to the    *)
  (* "Ready" state.  The client can send a request in "Ready" state and    *)
  (* becomes "Waiting" state to wait for response.  If the request is      *)
  (* handled by the server, the client becomes to "Done" state.  In the    *)
  (* "Done" state, the server can back to the "Ready" state to send        *)
  (* another message or be closed.                                         *)
  (*************************************************************************)
   {"Start", "Ready", "Waiting", "Done", "Closed"}

TypeInvariant == /\ clientStat \in [Client -> ClientStates]
                 /\ serverStat \in [Server -> ServerStates]
                 /\ msgs \subseteq Message

Init == /\ clientStat = [c \in Client |-> "Start"]
        /\ serverStat = [s \in Server |-> [stat |-> "Start", cur |-> NoVal]]
        /\ msgs = {}

-----------------------------------------------------------------------------

ClientOpen(c) ==
  /\ clientStat[c] = "Start"
  /\ clientStat' = [clientStat EXCEPT ![c] = "Ready"]
  /\ UNCHANGED <<serverStat, msgs>>

SendRequest(c) ==
  /\ clientStat[c] = "Ready"
  /\ clientStat' = [clientStat EXCEPT ![c] = "Waiting"]
  /\ msgs' = msgs \cup {[sender |-> c]}
  /\ UNCHANGED serverStat

Resend(c) ==
  /\ clientStat[c] = "Done"
  /\ clientStat' = [clientStat EXCEPT ![c] = "Ready"]
  /\ UNCHANGED <<serverStat, msgs>>

Close(c) ==
  /\ clientStat[c] = "Done"
  /\ clientStat' = [clientStat EXCEPT ![c] = "Closed"]
  /\ UNCHANGED <<serverStat, msgs>>

-----------------------------------------------------------------------------

ServerOpen(s) ==
   /\ serverStat[s].stat = "Start"
   /\ serverStat' = [serverStat EXCEPT ![s].stat = "Listening"]
   /\ UNCHANGED <<clientStat, msgs>>

Accept(s, m) ==
   /\ serverStat[s].stat = "Listening"
   /\ m \in msgs
   /\ msgs' = msgs \ {m}
   /\ serverStat' = [serverStat EXCEPT ![s].stat = "Processing",
                                       ![s].cur = m]
   /\ UNCHANGED clientStat

Process(s) ==
  /\ serverStat[s].stat = "Processing"
  /\ serverStat' = [serverStat EXCEPT ![s].stat = "Listening",
                                      ![s].cur = NoVal]
  /\ clientStat' = [clientStat EXCEPT ![serverStat[s].cur.sender] = "Done"]
  /\ UNCHANGED msgs

-----------------------------------------------------------------------------
  
Next ==
  \/ \E s \in Server : \/ ServerOpen(s)
                       \/ Process(s)
  \/ \E c \in Client : \/ ClientOpen(c)
                       \/ SendRequest(c)
                       \/ Resend(c)
                       \/ Close(c)
  \/ \E s \in Server, m \in msgs : Accept(s, m)

Spec == /\ Init /\ [][Next]_vars /\ WF_vars(Next)
        /\ \A c \in Client : SF_vars(Close(c))

-----------------------------------------------------------------------------

Termination ==
  (*************************************************************************)
  (* Eventually all the clients should be closed.                          *)
  (*************************************************************************)
  <>(\A c \in Client : clientStat[c] = "Closed")

Processed ==
  (*************************************************************************)
  (* If a client has sent a message and is in the "Waiting" state, the     *)
  (* message should be eventually processed by the server.                 *)
  (*************************************************************************)
  \A c \in Client : clientStat[c] = "Waiting" ~> clientStat[c] = "Done"

ValidProcessingMessage ==
  (*************************************************************************)
  (* The message processing by a server should be a valid message sent by  *)
  (* a client                                                              *)
  (*************************************************************************)
  [](\A s \in Server : serverStat[s].stat = "Processing" =>
                          serverStat[s].cur /= NoVal)

THEOREM Spec => Termination
THEOREM Spec => Processed
THEOREM Spec => ValidProcessingMessage

=============================================================================
\* Modification History
\* Last modified Sat Mar 03 20:43:29 EST 2018 by changjian
\* Created Thu Mar 01 14:11:58 EST 2018 by changjian
