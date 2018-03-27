------------------------------- MODULE ProCon -------------------------------
EXTENDS Integers

(***************************************************************************)
(* Producer is the set of all the producers.  Consumer is the set of all   *)
(* the consumers.  Max is the max number of products there can be in the   *)
(* system.                                                                 *)
(***************************************************************************)
CONSTANT Producer, Consumer, Max

(***************************************************************************)
(* Use ASSUME to asser that Max should be an integer.                      *)
(***************************************************************************)
ASSUME Max \in Int

VARIABLES size  \* The current number of the products.

TypeInv == size \in Int

Init == size = 0

Produce(p) ==
  (*************************************************************************)
  (* If the current size is less than Max, then the producer is able to    *)
  (* produce a product.                                                    *)
  (*************************************************************************)
  /\ size < Max
  /\ size' = size + 1

Consume(c) ==
  (*************************************************************************)
  (* If the current size is greater than 0, then the consumer is able to   *)
  (* retrieve a product.                                                   *)
  (*************************************************************************)
  /\ size > 0
  /\ size' = size - 1

Next == \/ \E p \in Producer : Produce(p)
        \/ \E c \in Consumer : Consume(c)

Spec == Init /\ [][Next]_size

SizeInv == [](size <= Max /\ size >= 0)

THEOREM Spec => SizeInv

=============================================================================
\* Modification History
\* Last modified Mon Mar 26 20:14:01 EDT 2018 by changjian
\* Created Thu Mar 08 22:35:51 EST 2018 by changjian
