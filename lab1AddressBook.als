module addressBook1
// Simple address book example
sig Name, Addr {}
sig Book {addr: Name -> lone Addr}
pred hasOneBook [] {#Book > 0}
pred everyNameAddressIsPairedInABook [b:Book,n:Name,a:Addr] {
    n -> a in b.addr
}

pred eachPairOnlyBelongsToOneBook [b1,b2:Book,n:Name,a:Addr]{
    n -> a in b1.addr && not(n -> a in b2.addr)
}

pred numberOfNamesExceedsAddresses [] {
    #Name > #Addr
}

pred moreThanOneBook [] {
    #Book > 1
}

pred atLeastOneNonEmptyBook [] {
    some b:Book | #{b.addr} > 0
}

pred assessedFiveA [] {
    some b1:Book | some b2:Book |
      b1 != b2 && #{b1.addr} > 0 && #{b2.addr} > 0 &&
      b1.addr != b2.addr
}

pred assessedFiveB [] {
    all b:Book | some b.addr
}

pred showImpossible [b:Book] {
    //            all addresses for name n
    some n:Name | #n.(b.addr) > 1
}

pred showMisleadinglyInconsistent {
    #Book > 5
}

pred add [b, b':Book, n:Name, a:Addr] {
    b'.addr = b.addr + n -> a
}

pred assessedNine [b,b':Book, n:Name, a:Addr] {
    add[b,b',n,a]
    b != b'
    Name.(b.addr) = Name.(b'.addr)
	!n in b.addr.Addr
}

pred del [b: Book, b': Book, n: Name, a: Addr] {
    b'.addr = b.addr - n -> a
}

pred isSameStateAfterDel [n:Name, a:Addr, b:Book, b':Book] {
    del[b,b',n,a]
    b'.addr = b.addr
	b != b'
}

pred assessedTwelve [n: Name, b: Book, b': Book] {
    b'.addr = b.addr - (n -> n.(b.addr))
}

//run assessedTwelve for 2 but exactly 2 Book

assert DelUndoesAdd
{ all b,b',b'':Book, n:Name, a:Addr |
(add[b,b',n,a] && del[b',b'',n,a])
=> b.addr = b''.addr
}
check DelUndoesAdd for 3
