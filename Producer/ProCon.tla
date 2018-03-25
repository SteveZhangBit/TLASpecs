------------------------------- MODULE ProCon -------------------------------
EXTENDS Integers

CONSTANT Producer, Consumer, Max

ASSUME Max \in Int

VARIABLES size

TypeInv == size \in Int

Init == size = 0

Produce(p) == /\ size < Max
              /\ size' = size + 1

Consume(c) == /\ size > 0
              /\ size' = size - 1

Next == \/ \E p \in Producer : Produce(p)
        \/ \E c \in Consumer : Consume(c)

Spec == Init /\ [][Next]_size

SizeInv == [](size <= Max /\ size >= 0)

THEOREM Spec => SizeInv

=============================================================================
\* Modification History
\* Last modified Fri Mar 23 10:08:37 EDT 2018 by changjian
\* Created Thu Mar 08 22:35:51 EST 2018 by changjian
