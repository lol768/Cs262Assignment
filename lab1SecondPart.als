module addressBook2
// The second address book model
abstract sig Target {}

//    Target
//    /   \
//  Addr <Name>
//       /  \
//    Alias  Group

sig Addr extends Target {}
abstract sig Name extends Target {}
sig Alias, Group extends Name {}

sig Book {
    addr: Name -> Target
}{ (no n:Name | n in n.^addr) && all a:Alias | one adr:Addr | (a.addr = adr or no a.addr)}

pred del[b,b':Book,n:Name,t:Target] {
    #(Name.(Book$0.addr) & n) = 0
    b'.addr = b.addr - n -> t
}

pred show [b,b':Book,n:Name,t:Target] {
    some b'.addr && del[b,b',n,t] &&
    b'.addr != b.addr
    //Name.^(b.addr) = Name.^(b'.addr)
    // some a:Addr | a in Name.(b.addr)
}
run show for 3 but 2 Book
