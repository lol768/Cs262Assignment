module studentMarks
sig Student, Tutor, Mark {}
sig Course {
    reg : set Student,
    alloc : Student -> Tutor,
    result : Student -> Mark
}
pred inv[c:Course] {
    inva[c] && invb[c]
}

pred inva[c:Course] {
    // (1) all registered students have tutors
    all s:(c.reg) | s.(c.alloc) != none

    // (2) every student with a tutor is reg'd
    all s:((c.alloc).Tutor) | c.reg & s != none

    // (3) no student can have > 1 tutor for a course
    no s:(c.reg) | #(s.(c.alloc)) > 1
}

pred invb[c:Course] {
    // (1) Only registered students can have a result
    c.reg <: c.result = c.result

    // (2) No student can have more than one mark for a course
    all s:(c.reg) | lone c.result[s]
}

pred atLeastOneStudentHasAMark[c:Course] {
    // We need at least one item in the result field :)
    some c.result
}


assert atLeastOneAllocatedStudent {
    all c:Course | some c.reg
}

fact ourFact {
    all c:Course | inv[c] && atLeastOneStudentHasAMark[c]
}

//check atLeastOneAllocatedStudent for 3 but exactly 1 Course

pred addReg[c,c':Course,s:Student] {
    s !in c.reg
    c'.reg = c.reg + s 
    some s.(c'.alloc) // we need *a* tutor, but don't care who
    c'.result = c.result
}

pred recordMark[c,c':Course, s:Student, m:Mark] {
    (c.reg & s) != none // student has to be reg'd
    (c.result)[s] = none // student has no mark already
    c'.reg = c.reg
    c'.result = c.result + s -> m
}

pred delReg[c,c':Course, s:Student] {
    (c.reg & s) != none // student reg'd
    (c.result)[s] = none // student has no mark already
    c'.reg = c.reg - s
    c'.alloc = c'.reg <: c.alloc // fix up tutors
    c'.result = c.result
}

fun havemark[c:Course, m:Mark] : set Student {
    (c.result).m
}

fun scores[s:Student] : Course -> Mark {
    {c:Course, m:Mark | m in s.(c.result)}
}

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


fun studentsWithGivenTutor[c:Course, t:Tutor] : set Student {
    (c.alloc).t
}

run {all c:Course | inv[c]} for 5 but exactly 2 Course
