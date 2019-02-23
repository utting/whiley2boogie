type Node is { int data, List next }
type List is null | &Node

method test():
    &Node aa = new (Node) {data:3, next:null}
    &Node bb = new (Node) {data:4, next:aa}
    assert *bb.data == 4
    List tail = *bb.next
    assert *tail.data == 3
    tail = *bb.next
    // assert tail == null    // Cannot verify this.  Why not?

