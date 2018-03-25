------------------------------ MODULE DieHard ------------------------------
EXTENDS Integers

VARIABLE small, big

TypeInvariant == /\ small \in 0 .. 3
                 /\ big   \in 0 .. 5

Init == /\ small = 0
        /\ big = 0

FillSmall == /\ small' = 3
             /\ big' = big

FillBig == /\ small' = small
           /\ big' = 5

SmallToBig == IF small + big <= 5
              THEN /\ big' = small + big
                   /\ small' = 0
              ELSE /\ big' = 5
                   /\ small' = small - (5 - big)

BigToSmall == IF small + big <= 3
             THEN /\ small' = small + big
                  /\ big' = 0
             ELSE /\ small' = 3
                  /\ big' = big - (3 - small)

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ big' = 0
            /\ small' = small

Next == \/ FillSmall
        \/ FillBig
        \/ SmallToBig
        \/ BigToSmall
        \/ EmptySmall
        \/ EmptyBig

=============================================================================
\* Modification History
\* Last modified Thu Dec 21 14:52:38 CST 2017 by changjian
\* Created Thu Dec 21 14:15:57 CST 2017 by changjian
