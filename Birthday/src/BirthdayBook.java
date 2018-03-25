import java.util.LinkedList;
import java.util.List;

/*
---------------------------- MODULE BirthdayBook ----------------------------
CONSTANT Name, Date, None

VARIABLES known, birthday

TypeInvariant == /\ known \subseteq Name
                 /\ birthday \in [Name -> Date \cup {None}]

StateInvariant == LET names == {name \in Name : birthday[name] /= None}
                  IN  known = names

AddBirthday(name, date) == /\ name \notin known
                           /\ known' = known \cup {name}
                           /\ birthday' = [birthday EXCEPT ![name] = date]

Init == /\ known = {}
        /\ birthday = [name \in Name |-> None]

Next == \E name \in Name : \E date \in Date : AddBirthday(name, date)

Spec == Init /\ [][Next]_<<known, birthday>>

THEOREM Spec => [](TypeInvariant /\ StateInvariant)

=============================================================================
\* Modification History
\* Last modified Mon Feb 26 20:20:17 EST 2018 by changjian
\* Created Sun Feb 25 21:07:01 EST 2018 by changjian
 */
public class BirthdayBook {

    /*
     * VARIABLES names
     */
    private List<String> names;
    /*
     * VARIABLES dates
     */
    private List<String> dates;
    /*
     * VARIABLES size
     */
    private int size = 0;

    /*
     * Init == /\ names = <<>>
     *         /\ dates = <<>>
     *         /\ size = 0
     */
    public BirthdayBook() {
        names = new LinkedList<>();
        dates = new LinkedList<>();
    }

    public BirthdayBook(List<String> names, List<String> dates) {
        this.names = names;
        this.dates = dates;
    }

    /*
     * For a method in Java, it can be translated to a TLA+ expression. The final values
     * of the class fields after running the method should be the post-conditions of the
     * TLA+ expression. The calling conditions of this method should be the pre-conditions
     * of the expression. In the following example, there are no pre-conditions.
     *
     * AddBirthdayBook(name, date) == IF notInNames(name)
     *                                  THEN /\ size' = size + 1
     *                                       /\ names' = Append(names, name)
     *                                       /\ dates' = Append(dates, date)
     *                                  ELSE /\ TRUE
     *                                       /\ UNCHANGED <<names, dates, size>>
     */
    public void addBirthday(String name, String date) {
        if (notInNames(name)) {
            /*
             * Another possible expression is to abstract part of the code. In this abstraction,
             * isInNames(name) becomes the precondition of the expression instead of using the
             * IF-THEN-ELSE expression in the previous example.
             *
             * AddBirthdayBook2(name, date) == /\ notInNames(name)
             *                                 /\ size' = size + 1
             *                                 /\ names' = Append(names, name)
             *                                 /\ dates' = Append(dates, date)
             */
            // start of the fragment
            ++size;
            names.add(name);
            dates.add(date);
            // end of the fragment
        }
    }

    /*
     * isInNames(name) == \A i \in 1 .. size : name /= names[i]
     */
    private boolean notInNames(String name) {
        return names.indexOf(name) == -1;
    }

}
