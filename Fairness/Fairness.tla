------------------------------ MODULE Fairness ------------------------------
VARIABLES pc

Init == pc = "1"

Step1 == pc = "1" /\ pc' = "2"

Step2 == pc = "2" /\ pc' = "Done"

StepBack == pc = "2" /\ pc' = "1"

Next == Step1 \/ Step2 \/ StepBack \/ (pc = "Done" /\ UNCHANGED pc)

Spec == /\ Init /\ [][Next]_pc
        /\ WF_pc(Step1) /\ WF_pc(StepBack) /\ SF_pc(Step2)

(***************************************************************************)
(* If we let TLC check Deadlock, it will produce the error that the spec   *)
(* meets deadlock because when pc = "Done", no further actions are         *)
(* enabled.  However, if we uncheck the "Deadlock" option, temporal        *)
(* formula Termination is still violated because the spec can stutter      *)
(* forever before pc = "Done".                                             *)
(***************************************************************************)
Termination == <>(pc = "Done")

=============================================================================
\* Modification History
\* Last modified Thu Feb 08 22:31:35 EST 2018 by changjian
\* Created Thu Feb 08 21:48:32 EST 2018 by changjian
