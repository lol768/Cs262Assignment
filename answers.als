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

pred assessedFiveA[] {
    some b1:Book | some b2:Book |
      b1 != b2 && #{b1.addr} > 0 && #{b2.addr} > 0 &&
      b1.addr != b2.addr
}

//
//  b) instances which could have any amount of books (depending on 
//     the run statement) but all books are non-empty.   
 
pred assessedFiveB[] {
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

pred showadd[b,b':Book, n:Name, a:Addr] {
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

pred assessedTwelve[n: Name, b: Book, b': Book] {
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

pred invb[c:Course] {
    // (1) Only registered students can have a result
    c.reg <: c.result = c.result

    // (2) No student can have more than one mark for a course
    all s:(c.reg) | lone c.result[s]
}

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

pred atLeastOneStudentHasAMark[c:Course] {
    // We need at least one item in the result field :)
    some c.result
}

run {all c:Course | inv[c] && atLeastOneStudentHasAMark[c]} for 3 but exactly 1 Course

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

pred addReg[c,c':Course,s:Student] {
    s !in c.reg
    c'.reg = c.reg + s // add student to set of registered students
    one t:s.(c'.alloc) | c'.alloc = c.alloc + s -> t // we need *a* tutor, but don't care who
    c'.result = c.result // this can safetly stay the same
}

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

pred recordMark[c,c':Course, s:Student, m:Mark] {
    (c.reg & s) != none // student has to be reg'd

    // NB: This disallows updating a mark, question suggests
    //     we're adding a mark entry: "input [...] a mark"
    (c.result)[s] = none // student has no mark already
    c'.reg = c.reg // students registered shouldn't change
    c'.alloc = c.alloc // tutor allocation shouldn't change
    c'.result = c.result + s -> m // new entry for this result is union'd
}

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

pred delReg[c,c':Course, s:Student] {
    (c.reg & s) != none // student reg'd
    (c.result)[s] = none // student has no mark already
    c'.reg = c.reg - s
    c'.alloc = c'.reg <: c.alloc // fix up tutors
    c'.result = c.result
}

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

fun havemark[c:Course, m:Mark] : set Student {
    (c.result).m
}
                                                                  
//  A function which takes student s as input; outputs the binary relation 
//  consisting of all course/mark pairs recorded for s.
//

fun scores[s:Student] : Course -> Mark {
    { c:Course, m:Mark | m in s.(c.result) }
}

                                                                    
//  A function which takes course c as input; outputs the set of tutors 
//  who are responsible for one or more students registered for c who do 
//  not yet have a mark. 
//

fun findtutors[c:Course] : set Tutor {
    // set of tutors responsible for >= 1 students:
    // * registered for c
    // * don't have a mark

    // tutors where...
    {t:Tutor |
        #( // the cardinality of intersection of..
            // students responsible for and
            (c.alloc).t & {s:Student |
                // students with no mark that are reg'd
                !(s in (c.result).Mark) && s in c.reg
            }
         ) >= 1 // is greater than or equal to 1
    }
}

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

pred init[c:Course] {
    // suitable initial state where course is empty
    no c.reg
    no c.alloc
    no c.result
}

//  - an alternative nondeterministic initialisation which would allow a trace to 
//    start from any state

pred nonDetInit[c:Course] {
    // any course is fine if it complies with inv
    inv[c]
}

//
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//
//  ASSESSED QUESTION   (5 marks)
//
//  QUESTION 8
//  ----------
//  Write a fact statement, traces, to describe the traces of the system

// NB: Using the deterministic init and non-deterministic addReg

fact traces {
    init[first[]]
    // iff not gives us xor-like functionality - we use this to enforce
    // only one operation happens between the old and new Course items
    all c: Course - last[] | let c' = next[c] | {
        (one s:Student | addReg[c,c',s] iff not delReg[c,c',s]) iff not
        (one s:Student, m:Mark | recordMark[c,c',s,m])
    }
}

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

pred atLeastOneScoreExists[] {
    scores[Student][Course] != none // using scores function defined above
}

run {atLeastOneScoreExists} for 3 but 3 Course

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

// I've seen a similar problem with "cannibals and missionaries"
// but not solved anything like these with Alloy.

// After running the model, I get the following solution:
// (1) Mon1 Mon2 mun1 mun2 | Boat Mon3 mun3
// (2) Boat Mon1 Mon2 mun1 mun2 mun3 | Mon3
// (3) mun1 mun2 mun3 | Boat Mon1 Mon2 Mon3
// (4) Boat Mon2 mun1 mun2 mun3 | Mon1 Mon3
// (5) Mon2 mun2 | Boat mun1 mun3 Mon1 Mon3
// (6) Boat Mon1 Mon2 mun1 mun2 | Mon3 mun3
// (7) Mon1 Mon2 | Boat Mon3 mun1 mun2 mun3
// (8) Boat Mon1 Mon2 Mon3 | mun1 mun2 mun3
// (9) Mon2 | Boat Mon1 Mon3 mun1 mun2 mun3
// (10) Boat Mon2 mun1 | Mon1 Mon3 mun2 mun3
// (11) | Boat Mon1 Mon2 Mon3 mun1 mun2 mun3

open util/ordering [PuzzleState]

abstract sig Entity {}
abstract sig Character extends Entity {}

one sig Boat extends Entity {}
sig Munchkin extends Character {}
sig Monster extends Character {}

sig PuzzleState { // represents a point in time
    leftOfRiver : set Entity,
    rightOfRiver : set Entity
} {
    // constraint 1 - sets must be disjoint
    // no characters can be on both sides of the river at one time
    leftOfRiver & rightOfRiver = none

    // constraint 2 - every entity must be accounted for
    Entity - (leftOfRiver+rightOfRiver) = none

    // constraint 3a - munchkins never outnumbered on LHS
    all mun:Munchkin | mun in leftOfRiver => (#(leftOfRiver & Monster) =< #(leftOfRiver & Munchkin))

    // constraint 3b - munchkins never outnumbered on RHS
    all mun:Munchkin | mun in rightOfRiver => (#(rightOfRiver & Monster) =< #(rightOfRiver & Munchkin))
}

pred init[p: PuzzleState] {
    // all characters start on the LHS in our model
    #{ mun:Munchkin | mun in p.leftOfRiver } = 3
    #{ mon:Monster | mon in p.leftOfRiver } = 3

    Boat in p.leftOfRiver // boat starts on the left too
}

pred validRightMove[p,p': PuzzleState] {
    // The boat is on the RHS afterwards, therefore RHS has has >=1 new character
    // These characters must come from the previous LHS so:
    // The difference between the intersection of all characters and those on the RHS afterwards
    // and the intersection of all characters and those on the RHS before is known as "gainedOnRight"

    // We enforce that it cannot be empty (some characters have to move), less than eq 2 characters can move (#gainedOnRight =< 2)
    // and the new left hand side (where the characters came from) must be deprived of all those characters in the new state.
    let gainedOnRight = (Character & p'.rightOfRiver) - (Character & p.rightOfRiver) |
        { gainedOnRight != none
          #gainedOnRight =< 2
          ((Character & p'.leftOfRiver)+gainedOnRight) = (Character & p.leftOfRiver) }
}

pred validLeftMove[p,p': PuzzleState] {
    // The boat is on the LHS afterwards, therefore LHS has has >=1 new character
    // These characters must come from the previous RHS
    let gainedOnLeft = (Character & p'.leftOfRiver) - (Character & p.leftOfRiver) |
        { gainedOnLeft != none
          #gainedOnLeft =< 2
          ((Character & p'.rightOfRiver)+gainedOnLeft) = (Character & p.rightOfRiver) }
}

pred validMove[p, p': PuzzleState] {
    // now the fun part! Ensuring steps are valid
    all b:Boat |
        (b in p'.leftOfRiver => (b not in p.leftOfRiver && validLeftMove[p,p'])) &&
        (b in p'.rightOfRiver => (b not in p.rightOfRiver && validRightMove[p,p']))
}

fact traces {
    init[first[]] // First state
    
    all psBefore: PuzzleState - last[] | let psAfter = next[psBefore] | validMove[psBefore, psAfter]
    let psFinal = last[] | #(psFinal.leftOfRiver) = 0 // everyone is on the right
}

// We know the optimal solution involves 11 steps from Wikipedia.
// Since we have a start state we constrain the model to 12 states in total.
run {} for 12 but exactly 6 Character, 1 Boat, 12 PuzzleState


//
////////////////////////////////////////////////////////////////////////////////





