sig SYM, VAL {}
sig SymTab {
    table: SYM -> lone VAL,
    reserved: set SYM
} { #(reserved & table.VAL) = 0 }

pred add[s,s':SymTab, sym:SYM,val:VAL]  {
    sym !in s.table.VAL
    sym !in s.reserved
    s'.table = s.table + sym -> val
    s'.reserved = s.reserved
}

pred del[s,s':SymTab, sym:SYM] {
    sym in s.table.VAL
    s'.table = s.table - sym -> VAL
    s'.reserved = s.reserved
}

// previously addres
pred addReserved[s,s':SymTab, sym:SYM] {
    sym !in s.table.VAL
    sym !in s.reserved
    s'.table = s.table
    s'.reserved = s.reserved + sym
}
