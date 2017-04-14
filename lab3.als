module studentMarks
open util/ordering [Course]
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

pred init[c:Course] {
    // suitable initial state where course is empty
    no c.reg
    no c.alloc
    no c.result
}

pred nonDetInit[c:Course] {
    // any course is fine if it complies with inv
    inv[c]
}

pred addReg[c,c':Course,s:Student] {
    s !in c.reg
    c'.reg = c.reg + s
    one t:s.(c'.alloc) | c'.alloc = c.alloc + s -> t // we need *a* tutor, but don't care who
    c'.result = c.result
}

pred recordMark[c,c':Course, s:Student, m:Mark] {
    (c.reg & s) != none // student has to be reg'd
    (c.result)[s] = none // student has no mark already
    c'.reg = c.reg
    c'.alloc = c.alloc // this shouldn't change!
    c'.result = c.result + s -> m
}

pred delReg[c,c':Course, s:Student] {
    (c.reg & s) != none // student reg'd
    (c.result)[s] = none // student has no mark already
    c'.reg = c.reg - s
    c'.alloc = c'.reg <: c.alloc // fix up tutors
    c'.result = c.result
}


fact traces {
    init[first[]]
    // iff not gives us xor-like functionality - we use this to enforce
    // only one operation happens between the old and new Course items
    all c: Course - last[] | let c' = next[c] | {
        (one s:Student | addReg[c,c',s] iff not delReg[c,c',s]) iff not
        (one s:Student, m:Mark | recordMark[c,c',s,m])
    }
}

fun scores[s:Student] : Course -> Mark {
    {c:Course, m:Mark | m in s.(c.result)}
}

pred atLeastOneScoreExists[] {
    scores[Student] != none
}

run {atLeastOneScoreExists} for 3 but 3 Course, 2 Tutor
