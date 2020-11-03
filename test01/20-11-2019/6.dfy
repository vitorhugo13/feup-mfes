// File system node
trait Node {

    const name: string; // unique within each folder
    ghost const depth: nat; // starts in 0 at file system root
}

 class {:autocontracts} File extends Node { }

 class {:autocontracts} Folder extends Node {
   var child: set<Node>; 

    predicate Valid() {
        // TODO
    }

     constructor (name: string, parent: Folder?) {
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