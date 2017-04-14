open util/ordering[Time] as TO

sig SYM, VAL, Time {}

one sig SymTab {
    table: SYM -> VAL -> Time,
    reserved: Time -> set SYM
} {
    all t:Time | #(reserved[t] & (table.t).VAL) = 0
    all s:SYM, t:Time | lone s.table.t
}

// add symbol->value pair
pred add[s:SymTab, sym:SYM, val:VAL, t,t':Time] {
    sym !in t.(s.reserved)
    sym !in s.table.t.VAL
    s.table.t' = s.table.t + sym -> val
    t.(s.reserved) = t'.(s.reserved)
}

// delete symbol
pred del[s:SymTab, sym:SYM, t,t':Time] {
    sym in s.table.t.VAL
    s.table.t' = s.table.t - sym -> VAL
    t.(s.reserved) = t'.(s.reserved)
}

// add reserved
pred addres[s:SymTab, sym:SYM, t,t':Time] {
    sym !in t.(s.reserved)
    sym !in s.table.t.VAL
    s.table.t = s.table.t'
    t'.(s.reserved) = t.(s.reserved) + sym
}

pred init[t:Time] {
    one s:SymTab | { 
        t.(s.reserved) = none
        s.table.t.VAL = none
    }
}

fun reservedSetEmptyTimes[s:SymTab] : set Time {
    { t:Time | t.(s.reserved) = none }
}

pred symbolInTableAtTime[s:SymTab, sym:SYM, t:Time] {
    sym in s.table.t.VAL
}

fact traces {
    init[TO/first[]]
    all t:Time - TO/last[] | let t' = TO/next[t] | one s:SymTab, sym:SYM | del[s,sym,t,t'] iff not addres[s,sym,t,t'] iff not (one v:VAL | add[s,sym,v,t,t'])
}

run {} for 2
