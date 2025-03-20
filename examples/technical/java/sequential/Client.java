class HashSetClient {

    //@ ensures Perm(contents, write);
    //@ ensures contents == set<Client>{} && this != null;
    public HashSetClient() {};

    //@ ghost set<Client> contents = set<Client>{};

    //@ decreases;
    //@ requires Perm(contents, write);
    //@ ensures Perm(contents, write);
    //@ ensures contents == \old(contents + set<Client> { c });
    public void put(Client c);

    //@ decreases;
    //@ requires Perm(contents, read);
    //@ ensures \result == c \in contents;
    public /*@ pure @*/ boolean contains(Client c);

}


/*@
  static_level 7;
  static_invariant Perm(ids, write) ** ids >= 0;
  static_invariant Perm(allocs, write) ** allocs != null ** Perm(allocs.contents, write);
  static_invariant (\forall* Client c; allocs.contains(c) ==> Perm({: c.id :}, 1\2));
  static_invariant (\forall Client c; allocs.contains(c) ==> {: c.id :} < ids);
  static_invariant (\forall Client c1, Client c2; allocs.contains(c1) && allocs.contains(c2) && c1 != c2
                    ==> {:c1.id:} != {:c2.id:});
@*/
class Client {
    int id;
    static int ids;
    //@ ghost static HashSetClient allocs;

    /*@
      static_level 6;
    @*/
    static {
        ids = 0;
        //@ ghost allocs = new HashSetClient();
    }

    //@ decreases;
    //@ static_level 8;
    //@ ensures Perm(this.id, 1\2);
    public Client() {
        //@ openInv Client write;
        id = ids;
        ids = ids + 1;
        //@ ghost allocs.put(this);
        //@ closeInv Client write;
    }
}