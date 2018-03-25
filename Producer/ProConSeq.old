----------------------------- MODULE ProConSeq -----------------------------
EXTENDS Sequences, Integers, TLC

CONSTANT Producer, Consumer

(* --algorithm PC
  variables queue = <<>>, locker = "unlock";
  define
    Max == 3
  end define;
  
  macro Lock()
  begin
    await locker = "unlock";
    locker := "lock";
  end macro;
  
  macro Unlock()
  begin
    locker := "unlock";
  end macro;
  
  process producer \in Producer
  begin
    l1: while TRUE do
\*    l2:   Lock();
    l3:   if Len(queue) < Max then
    l4:     queue := Append(queue, <<"Product">>);
          end if;
\*    l5:   Unlock();
        end while;
  end process;

  process consumer \in Consumer
  begin
    l1: while TRUE do
\*    l2:   Lock();
    l3:   if Len(queue) > 0 then
    l4:     queue := Tail(queue);
          end if;
\*    l5:   Unlock();
        end while;
  end process;
end algorithm*)
\* BEGIN TRANSLATION
\* Label l1 of process producer at line 25 col 9 changed to l1_
\* Label l3 of process producer at line 27 col 11 changed to l3_
\* Label l4 of process producer at line 28 col 13 changed to l4_
VARIABLES queue, locker, pc

(* define statement *)
Max == 3


vars == << queue, locker, pc >>

ProcSet == (Producer) \cup (Consumer)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ locker = "unlock"
        /\ pc = [self \in ProcSet |-> CASE self \in Producer -> "l1_"
                                        [] self \in Consumer -> "l1"]

l1_(self) == /\ pc[self] = "l1_"
             /\ pc' = [pc EXCEPT ![self] = "l3_"]
             /\ UNCHANGED << queue, locker >>

l3_(self) == /\ pc[self] = "l3_"
             /\ IF Len(queue) < Max
                   THEN /\ pc' = [pc EXCEPT ![self] = "l4_"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "l1_"]
             /\ UNCHANGED << queue, locker >>

l4_(self) == /\ pc[self] = "l4_"
             /\ queue' = Append(queue, <<"Product">>)
             /\ pc' = [pc EXCEPT ![self] = "l1_"]
             /\ UNCHANGED locker

producer(self) == l1_(self) \/ l3_(self) \/ l4_(self)

l1(self) == /\ pc[self] = "l1"
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << queue, locker >>

l3(self) == /\ pc[self] = "l3"
            /\ IF Len(queue) > 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << queue, locker >>

l4(self) == /\ pc[self] = "l4"
            /\ queue' = Tail(queue)
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED locker

consumer(self) == l1(self) \/ l3(self) \/ l4(self)

Next == (\E self \in Producer: producer(self))
           \/ (\E self \in Consumer: consumer(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

ProCon == INSTANCE ProCon WITH size <- Len(queue)

THEOREM Spec => ProCon!Spec
THEOREM Spec => ProCon!SizeInv

=============================================================================
\* Modification History
\* Last modified Fri Mar 23 10:09:06 EDT 2018 by changjian
\* Created Thu Mar 08 22:34:49 EST 2018 by changjian
