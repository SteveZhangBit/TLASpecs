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
    l2:   Lock();   \* Lock the queue to avoid data racing.
    l3:   if Len(queue) < Max then
    l4:     queue := Append(queue, <<"Product">>);
          end if;
    l5:   Unlock();
        end while;
  end process;

  process consumer \in Consumer
  begin
    l1: while TRUE do
    l2:   Lock();   \* Lock the queue to avoid data racing.
    l3:   if Len(queue) > 0 then
    l4:     queue := Tail(queue);
          end if;
    l5:   Unlock();
        end while;
  end process;
end algorithm*)
\* BEGIN TRANSLATION
\* Label l1 of process producer at line 25 col 9 changed to l1_
\* Label l2 of process producer at line 14 col 5 changed to l2_
\* Label l3 of process producer at line 27 col 11 changed to l3_
\* Label l4 of process producer at line 28 col 13 changed to l4_
\* Label l5 of process producer at line 20 col 5 changed to l5_
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
             /\ pc' = [pc EXCEPT ![self] = "l2_"]
             /\ UNCHANGED << queue, locker >>

l2_(self) == /\ pc[self] = "l2_"
             /\ locker = "unlock"
             /\ locker' = "lock"
             /\ pc' = [pc EXCEPT ![self] = "l3_"]
             /\ queue' = queue

l3_(self) == /\ pc[self] = "l3_"
             /\ IF Len(queue) < Max
                   THEN /\ pc' = [pc EXCEPT ![self] = "l4_"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "l5_"]
             /\ UNCHANGED << queue, locker >>

l4_(self) == /\ pc[self] = "l4_"
             /\ queue' = Append(queue, <<"Product">>)
             /\ pc' = [pc EXCEPT ![self] = "l5_"]
             /\ UNCHANGED locker

l5_(self) == /\ pc[self] = "l5_"
             /\ locker' = "unlock"
             /\ pc' = [pc EXCEPT ![self] = "l1_"]
             /\ queue' = queue

producer(self) == l1_(self) \/ l2_(self) \/ l3_(self) \/ l4_(self)
                     \/ l5_(self)

l1(self) == /\ pc[self] = "l1"
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << queue, locker >>

l2(self) == /\ pc[self] = "l2"
            /\ locker = "unlock"
            /\ locker' = "lock"
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ queue' = queue

l3(self) == /\ pc[self] = "l3"
            /\ IF Len(queue) > 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << queue, locker >>

l4(self) == /\ pc[self] = "l4"
            /\ queue' = Tail(queue)
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED locker

l5(self) == /\ pc[self] = "l5"
            /\ locker' = "unlock"
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ queue' = queue

consumer(self) == l1(self) \/ l2(self) \/ l3(self) \/ l4(self) \/ l5(self)

Next == (\E self \in Producer: producer(self))
           \/ (\E self \in Consumer: consumer(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

ProCon == INSTANCE ProCon WITH size <- Len(queue)

THEOREM Spec => ProCon!Spec
THEOREM Spec => ProCon!SizeInv

=============================================================================
\* Modification History
\* Last modified Mon Mar 26 20:14:49 EDT 2018 by changjian
\* Created Thu Mar 08 22:34:49 EST 2018 by changjian
