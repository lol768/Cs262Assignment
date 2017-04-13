//        LABSHEET - For WRITING SOLUTIONS TO ASSESSED QUESTIONS
//  
//  Hand in is by Tabula. Deadline is Thursday 20th April at 12 noon.
//
//  Please provide your answers to the lab questions in the spaces below. 
//  You can use comments to answer any textual questions and to provide any 
//  further information or explanations about the Alloy definitions you write. 
//  But please DON'T comment out your actual Alloy solutions.   
//
//  You SHOULD NOT convert the file to another format as I need to be able to
//  run your answers in Alloy. 
// 
//

//////////////////////////////////////////////////////////////////////////////////
//
//  LAB 1 - for writing your answers to the assessed questions from Lab 1
//  
//////////////////////////////////////////////////////////////////////////////////


module addressBook1
// Simple address book example
sig Name,Addr {}
sig Book {addr: Name -> lone Addr}



////////////////////////////////////////////////////////////////////
//                                                                
//  ASSESSED QUESTION   (6 marks)                                     
//
//  QUESTION 5. 
//  ----------
//  Write pred statements to display:                         
//  a) two books, both non-empty and which have different contents 
//     (that is, the mappings in their addr components are different) 

pred assessedFiveA [] {
    some b1:Book | some b2:Book |
      b1 != b2 && #{b1.addr} > 0 && #{b2.addr} > 0 &&
      b1.addr != b2.addr
}

//
//  b) instances which could have any amount of books (depending on 
//     the run statement) but all books are non-empty.   
 
pred assessedFiveB [] {
    all b:Book | some b.addr
}         

//
////////////////////////////////////////////////////////////////////




////////////////////////////////////////////////////////////////////
//                                                                
//  ASSESSED QUESTION   (5 marks)                                         
//
//  QUESTION 9.
//  ----------
//   Modify showadd to see an instance where a new name is added 
//   to the address book, but the set of addresses used doesn't change. 
// 

pred showadd [b,b':Book, n:Name, a:Addr] {
    add[b,b',n,a]
    b != b'
    Name.(b.addr) = Name.(b'.addr)
    !n in b.addr.Addr
}

//
////////////////////////////////////////////////////////////////////




////////////////////////////////////////////////////////////////////
//                                                                
//  ASSESSED QUESTION    (4 marks)                                 
//
//  QUESTION 12.
//  -----------
//  Write a pred to define del without an input address.
//

pred assessedTwelve [n: Name, b: Book, b': Book] {
    // TODO: revisit re b' == b || b' != b
    b'.addr = b.addr - (n -> n.(b.addr))
}

//
//
////////////////////////////////////////////////////////////////////




////////////////////////////////////////////////////////////////////
//                                                                
//  ASSESSED QUESTION   (5 marks)                                      
//
//  QUESTION 14.
//  -----------
//  Give a specific example of before and after states which 
//  illustrate this problem. What constraint could be added 
//  to del as a precondition to prevent it?
//

// Let b be the Book containing the following for the addr binary relation:
// 
// * Group$0 -> Alias$0
// * Group$1 -> Alias$0
// * Alias$0 -> Addr$0
// 
// Fig 1:
//   +--------------------------------------+
//   | Group$0                              |
//   |  (and)  ---->  Alias$0  ----> Addr$0 |
//   | Group$1                              |
//   +--------------------------------------+
// 
// Then, let b' be the Book following the delete operation where addr is:
// 
// * Group$0 -> Alias$0
// * Group$1 -> Alias$0
// 
// This is achieved where n:Name is Alias$0 and t:Target is Addr$0. Now notice
// that previously, every Name pointed (perhaps indirectly) to an address, Addr$0.
// With b' following the delete operation, the groups only point at an alias
// which doesn't have a corresponding entry in the same addr field.
// 
// To fix this, we can add a constraint to the del operation, changing the predicate
// to look like: 

pred del[b,b':Book,n:Name,t:Target] {
    Name.(b.addr) & n = none
    b'.addr = b.addr - n -> t
}

// We use the dot relational join to find all targets in the starting state's book. We
// take this set of targets and find the intersection of this and the name to be removed.
// If the intersection is the empty set (none in alloy), then the name to be removed is not
// a target in the rest of the address book.

//
////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////////
//
//  LAB 2 - for writing your answers to the assessed questions from Lab 2
//  
///////////////////////////////////////////////////////////////////////////

sig Student, Tutor, Mark {} 
sig Course { 
    reg : set Student, 
    alloc : Student -> Tutor, 
    result : Student -> Mark 
}

pred inv [c:Course] { 
    inva[c] && invb[c]
}

////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (4 marks)
//
//  QUESTION 2a.                           
//  ----------
//  Write the "invb" predicate for the remaining 2 requirements of the invariant.    
//


//
/////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (3 marks)
//
//  QUESTION 2b.                           
//  ----------
//  Write pred and run statements to find an instance which obeys 
//  all the invariant properties and in which at least one student has a mark.
//


//
/////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (4 marks)
//
//  QUESTION 5.
//  ----------
//  Provide the nondeterministic version of addReg. (Here, the name of the 
//  predicate only has been given - you'll need to write everything else.)
//  
pred addReg


//
/////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (4 marks)
//
//  QUESTION 7. 
//  ----------
//  Write an operation to input and record a mark for a student
//
pred recordMark


//
/////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (4 marks)
//
//  QUESTION 8.
//  ----------
//  Write the delReg operation.
//
pred delReg


//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (6 marks)
//
//  QUESTION 10
//  ----------
// 
//  A function which takes mark m and course c as inputs; outputs the set of 
//  all students who've scored m on course c.  
//

fun havemark 

                                                                  
//  A function which takes student s as input; outputs the binary relation 
//  consisting of all course/mark pairs recorded for s.
//

fun scores

                                                                    
//  A function which takes course c as input; outputs the set of tutors 
//  who are responsible for one or more students registered for c who do 
//  not yet have a mark. 
//

fun findtutors


//
//////////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////////
//
//  LAB 3 - for writing your answers to the assessed questions from Lab 3
//  
//////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (4 marks)
//
//  QUESTION 7
//  ----------
//  Write:
//  - a predicate, init, to describe the initial states of the system


//  - an alternative nondeterministic initialisation which would allow a trace to 
//    start from any state


//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (5 marks)
//
//  QUESTION 8
//  ----------
//  Write a fact statement, traces, to describe the traces of the system


//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (4 marks)
//
//  QUESTION 9
//  ----------
//  Write a pred statement and a run statement which  will display a trace in which 
//  some marks are obtained at some point.


//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (5 marks)
//
//  QUESTION 10
//  ----------
//  Write an assert statement to the effect that once a mark is entered for any 
//  student then the student always has a mark for that course. Provide a suitable 
//  check statement to try this out.


//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (4 marks)
//
//  QUESTION 12
//  ----------
//  Write modified signatures for the SymTab specification to model time


//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (4 marks)
//
//  QUESTION 13
//  ----------
//  Write modified add and delete operations for the approach with time.


//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (4 marks)
//
//  QUESTION 14
//  -----------
//  Write:
//  - a function which, for a given SymTab, outputs all times at which its 
//  - reserved set is empty


//  - a pred which is true for a SymTab, a symbol and a time if the symbol 
//  - is in the SymTab's table at that time


//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  EXTRA CHALLENGE
//
//  If you managed to get the munchkins and monsters across the river 
//  write your solution here.


//
////////////////////////////////////////////////////////////////////////////////





