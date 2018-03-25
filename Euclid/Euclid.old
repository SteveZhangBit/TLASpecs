------------------------------- MODULE Euclid -------------------------------
EXTENDS Naturals, TLC

CONSTANT U, V

gcd(u, v) == CHOOSE i \in 1 .. u :
                /\ u % i = 0
                /\ v % i = 0
                /\ \A j \in 1 .. u : /\ u % j = 0
                                     /\ v % j = 0
                                     => i >= j

\* PlusCal options (-termination)
(* --algorithm EuclidAlg
  variables u = U; v = V;
  begin
    while (u /= 0) do
      if (u < v) then
        u := v || v := u;
      end if;
      u := u - v;
    end while;
    assert v = gcd(U, V)
  end algorithm *)
\* BEGIN TRANSLATION
VARIABLES u, v, pc

vars == << u, v, pc >>

Init == (* Global variables *)
        /\ u = U
        /\ v = V
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF (u /= 0)
               THEN /\ IF (u < v)
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(v = gcd(U, V), 
                              "Failure of assertion at line 23, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ u' = u - v
         /\ pc' = "Lbl_1"
         /\ v' = v

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Mar 09 14:58:07 EST 2018 by changjian
\* Created Sun Jan 28 16:03:58 EST 2018 by changjian
