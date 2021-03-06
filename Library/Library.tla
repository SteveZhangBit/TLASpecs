----------------------------- MODULE Library -----------------------------
EXTENDS Integers, FiniteSets

(***************************************************************************)
(* Author defines the set of all the authors.  Title defines the set of    *)
(* all the book titles.  Subject defines the set of all the book subjects. *)
(* CopyID defines the set of all the ids of book copies.                   *)
(***************************************************************************)
CONSTANT Author, Title, Subject, CopyID

\* The record type representing the book copies.
Copy == [author : Author,
         title : Title,
         subjects : SUBSET Subject,
         id : CopyID]

(***************************************************************************)
(* RealPerson defines the set of all the real people which are able to     *)
(* borrow book from the library.  Nobody is a special "person" indicating  *)
(* that the book copy has not been borrowed yet.                           *)
(***************************************************************************)
CONSTANT RealPerson, Nobody

(***************************************************************************)
(* Define Person to be the union of RealPerson and Nobody.  Person is used *)
(* in Data definition indicating who has borrowed a book.                  *)
(***************************************************************************)
Person == RealPerson \cup {Nobody}

(***************************************************************************)
(* Data is a record type defining the check-out status of a book.          *)
(* lastuser is the last person who borrowed the book, and status is the    *)
(* status of the book either "out" or "in".                                *)
(***************************************************************************)
Data == [lastuser : Person, status : {"out", "in"}]

(***************************************************************************)
(* Max is a constant indicating the max amount of books a person can       *)
(* borrow from the library.  Use ASSUME to assert that Max should be a     *)
(* natural number.                                                         *)
(***************************************************************************)
CONSTANT Max
ASSUME Max \in Nat

VARIABLES
  books,    \* The set of all the copys in the library.
  records,  \* A function from Copy to "Data", where "Data" is a record with
            \* "lastuser" and "status".
  users,    \* The set of all the users who have regestiered in the library.
  staff,    \* The set of all the workers in the library.
  out       \* out defines the output of the system which should be a tuple.

\* A special null value indicating the book has not been added to the library.
CONSTANT NullData

LibraryTypeInvariant ==
  (*************************************************************************)
  (* Type invariant asserts the "types" of the variables.  Since TLA+ is   *)
  (* untyped, so the type invariant is mainly asserting that the value of  *)
  (* a variable is an element of some set of values.                       *)
  (*************************************************************************)
  /\ books \subseteq Copy
  /\ records \in [Copy -> Data \cup {NullData}]
  /\ users \subseteq RealPerson
  /\ staff \subseteq RealPerson

LibraryBookInvariant ==
  /\ \A b1, b2 \in books : b1.id = b2.id <=> b1 = b2
  (*************************************************************************)
  (* We cannot define /\ DOMAIN records = books here, since records is     *)
  (* total function.                                                       *)
  (*************************************************************************)
  /\ \A user \in users :
        LET outbooks == {b \in books : /\ records[b].lastuser = user
                                       /\ records[b].status = "out"}
        \* Checking the number of books a person borrowed
        \* should be less than Max
        IN  Cardinality(outbooks) <= Max

LibraryInit ==
  /\ books = {}
  /\ records = [b \in Copy |-> NullData]
  \* Choosing a random person from RealPerson as a initial user.
  /\ users = {CHOOSE p \in RealPerson : TRUE}
  \* Choosing a random person from RealPerson as a initial staff.
  /\ staff = {CHOOSE p \in RealPerson : TRUE}
  /\ out = <<>>

(***************************************************************************)
(* The helper function for accessing control.  It returns wether the doer  *)
(* is a member of staff.                                                   *)
(***************************************************************************)
restricted(doer) == doer \in staff

(***************************************************************************)
(* The helper function for accessing control.  It returns wether the doer  *)
(* is a member of staff or one of the users.                               *)
(***************************************************************************)
unrestricted(doer) == doer \in staff \cup users

AddBookCopy(book) ==
  (*************************************************************************)
  (* Add a book to the library.  The book should not be in the library and *)
  (* should have unique id.  The initial state for the book is [lastuser   *)
  (* |-> Nobody, status |-> "in"]                                          *)
  (*************************************************************************)
  /\ book \notin books
  /\ \A b \in books : b.id # book.id
  /\ books' = books \cup {book}
  /\ records' = [records EXCEPT ![book] = [lastuser |-> Nobody,
                                           status |-> "in"]]
  /\ out' = <<"ok">>
  /\ UNCHANGED <<users, staff>>

RemoveBookCopy(book) ==
  (*************************************************************************)
  (* Remove a book from the library.  The book should be already in the    *)
  (* library.  Removing should set the book record to null.                *)
  (*************************************************************************)
  /\ book \in books
  /\ books' = books \ {book}
  /\ records' = [records EXCEPT ![book] = NullData]
  /\ out' = <<"ok">>
  /\ UNCHANGED <<users, staff>>

BooksByAuthor(author) ==
  (*************************************************************************)
  (* A query.  Returns all the books by an author's name.                  *)
  (*************************************************************************)
  /\ out' = <<"ok", {b \in books : b.author = author}>>
  /\ UNCHANGED <<books, records, users, staff>>

SafeAddBookCopy(doer, book) ==
  (*************************************************************************)
  (* Only staff members can add book copies to the library.                *)
  (*************************************************************************)
  /\ restricted(doer)
  /\ AddBookCopy(book)

SafeRemoveBookCopy(doer, book) ==
  (*************************************************************************)
  (* Only staff members can remove book copies from the library.           *)
  (*************************************************************************)
  /\ restricted(doer)
  /\ RemoveBookCopy(book)

SafeBooksByAuthor(doer, author) ==
  (*************************************************************************)
  (* Both staff and users are able to search books by author from the      *)
  (* library.                                                              *)
  (*************************************************************************)
  /\ unrestricted(doer)
  /\ BooksByAuthor(author)

RobustAddBookCopy(doer, book) ==
  (*************************************************************************)
  (* Only staff members can add book copies to the library.  If the "doer" *)
  (* is not a staff member, the system should return error message.        *)
  (*************************************************************************)
  IF restricted(doer) THEN
    AddBookCopy(book)
  ELSE
    /\ out' = <<"doer is not a member of staff">>
    /\ UNCHANGED <<books, records, users, staff>>

RobustRemoveBookCopy(doer, book) ==
  (*************************************************************************)
  (* Only staff members can remove book copies from the library.  If the   *)
  (* "doer" is not a member of staff, the system should return error       *)
  (* message.                                                              *)
  (*************************************************************************)
  IF restricted(doer) THEN
    RemoveBookCopy(book)
  ELSE
    /\ out' = <<"doer is not a member of staff">>
    /\ UNCHANGED <<books, records, users, staff>>

CheckOutBook(book, borrower) ==
  (*************************************************************************)
  (* It represents a user borrows a book from the library.  The book       *)
  (* should be already in the library and not be checked out.              *)
  (*************************************************************************)
  /\ book \in books
  /\ records[book].status = "in"
  /\ records' = [records EXCEPT ![book].lastuser = borrower,
                                ![book].status = "out"]                               
  /\ out' = <<"ok">>
  /\ UNCHANGED <<users, books, staff>>

RobustCheckOutBook(book, borrower) ==
  (*************************************************************************)
  (* A robust version of checking out book.  The borrower should be in the *)
  (* user set.  Also, the user should not have been checked out books      *)
  (* equal or greater than Max.                                            *)
  (*************************************************************************)
  /\ borrower \in users \* The borrower should be a registered user.
  /\ LET outbooks == {b \in books : /\ records[b].lastuser = borrower
                                    /\ records[b].status = "out"}
     IN  Cardinality(outbooks) < Max
  /\ CheckOutBook(book, borrower)

CheckInBook(book, borrower) ==
  (*************************************************************************)
  (* A borrower returns a book to the library.  The book should be already *)
  (* in the library and marked as "out".                                   *)
  (*************************************************************************)
  /\ book \in books
  /\ records[book] = [lastuser |-> borrower, status |-> "out"]
  /\ records' = [records EXCEPT ![book].status = "in"]
  /\ out' = <<"ok">>
  /\ UNCHANGED <<users, books, staff>>

LibraryNext ==
  \/ \E book \in Copy:
        \/ AddBookCopy(book)
        \/ RemoveBookCopy(book)
  \/ \E book \in Copy, borrower \in RealPerson :
        \/ CheckOutBook(book, borrower)
        \/ CheckInBook(book, borrower)
  \/ \E author \in RealPerson :
        \/ BooksByAuthor(author)

RobustLibraryNext ==
  \/ \E book \in Copy, doer \in RealPerson:
        \/ RobustAddBookCopy(doer, book)
        \/ RobustRemoveBookCopy(doer, book)
  \/ \E book \in Copy, borrower \in Person :  \* Use Person here to let Nobody
                                              \* try to check out books
        \/ RobustCheckOutBook(book, borrower) 
        \/ CheckInBook(book, borrower)
  \/ \E doer, author \in RealPerson :
        \/ SafeBooksByAuthor(doer, author)

LibrarySpec ==
  /\ LibraryInit
  /\ [][LibraryNext]_<<books, records, users, staff, out>>

LibraryInvariant == [](LibraryTypeInvariant /\ LibraryBookInvariant)

THEOREM LibrarySpec => LibraryInvariant

=============================================================================
\* Modification History
\* Last modified Mon Mar 26 19:47:15 EDT 2018 by changjian
\* Created Wed Jan 17 21:31:30 EST 2018 by changjian
