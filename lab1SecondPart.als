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
}{no n:Name | n in n.^addr}

//fact noCircularity {
//    no n:Name | n in n.^addr
//}

pred show [b:Book] {
    some b.addr
    // some a:Addr | a in Name.(b.addr)
}
run show for 3 but 1 Book
