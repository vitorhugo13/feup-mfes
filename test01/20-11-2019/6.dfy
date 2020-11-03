// File system node
trait Node {

    const name: string; // unique within each folder
    ghost const depth: nat; // starts in 0 at file system root
}

 class {:autocontracts} File extends Node { }

 class {:autocontracts} Folder extends Node {
   var child: set<Node>; 

    predicate Valid() {
        //(i)names of child nodes are unique (no duplicates) 
        forall x, y :: x in child && y in child && x != y ==> x.name != y.name
        //(ii)the depth of child nodes is the depth of this node plus one
        && forall children :: children in child ==> children.depth == this.depth + 1
    }

     constructor (name: string, parent: Folder?)
        modifies parent
        requires |name| > 0
        ensures this.name == name
        ensures this.child == {}
        ensures parent != null ==> parent.child == parent.child + {this} && this.depth == parent.depth + 1
        ensures parent == null ==> this.depth == 0
    {
       // this object initialization
        this.name := name;
        this.depth := if parent == null then 0 else parent.depth + 1;
        this.child := {};
        // other objets' updates (after special "new" keyword)
        new;
        if parent != null {
            parent.child := parent.child + {this};
        }
    }
}