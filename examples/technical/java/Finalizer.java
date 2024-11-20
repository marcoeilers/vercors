
/*@ lock_invariant Perm(Finalizer.unfinalized, write) ** Perm(Finalizer.allocs, 1\2) ** (Finalizer.unfinalized != null ==> (Finalizer.unfinalized \in Finalizer.allocs)) **
                   (\forall* int i, int j; 0 <= i && i < j && j < |Finalizer.allocs|; Finalizer.allocs[i] != Finalizer.allocs[j]) **
                   (\forall* int i; 0 <= i && i < |Finalizer.allocs|;
                        Perm(Finalizer.allocs[i].next, write) ** Perm(Finalizer.allocs[i].prev, write) **
                        (Finalizer.allocs[i] != null) **
                        (Finalizer.allocs[i].prev == (i == 0 ? null : Finalizer.allocs[i - 1])) **
                        (Finalizer.allocs[i].next == (i == |Finalizer.allocs| - 1 ? null : Finalizer.allocs[i + 1])))
                        ** (|Finalizer.allocs| == 0 ? Finalizer.unfinalized == null : Finalizer.allocs[0] == Finalizer.unfinalized);
 */
class FinalizerLock {
    //@ decreases;
    public FinalizerLock() {
        // some implementation
    }

}

//@ resource finalizePre(Object o);
class JavaLangAccess {
    //@ static_level 2;
    //@ requires finalizePre(finalizee);
    public void invokeFinalize(Object finalizee) {
        // some implementation
    }
}

//@ static_level 3;
//@ static_invariant Perm(Finalizer.allocs, 1\2);
//@ dup_static_invariant Perm(Finalizer.lock, read) ** Finalizer.lock != null ** committed(Finalizer.lock);
class Finalizer {
    // inherited from Reference
    private Object referent;

    //@ context Perm(referent, write);
    //@ ensures referent == null;
    public void clear() {
        this.referent = null;
    }

    //@ requires Perm(referent, read);
    public /*@ pure @*/ Object get() {
        return this.referent;
    }

    //@ ghost static seq<Finalizer> allocs;

    /** Head of doubly linked list of Finalizers awaiting finalization. */
    private static Finalizer unfinalized = null;

    /** Lock guarding access to unfinalized list. */
    private static FinalizerLock lock;

    // implicit static_level 2;
    static {
        lock = new FinalizerLock();
        //@ ghost allocs = seq<Finalizer>{};
        //@ commit lock;
    }

    private Finalizer next, prev;

    //@ static_level 3;
    //@ requires finalizePre(finalizee) ** Perm(Finalizer.allocs, 1\2);
    //@ ensures Perm(Finalizer.allocs, 1\2) ** this \in Finalizer.allocs;
    private Finalizer(Object finalizee) {
        //@ openDupInv Finalizer;

        // push onto unfinalized
        synchronized (lock) {
            if (unfinalized != null) {
                this.next = unfinalized;
                unfinalized.prev = this;
            }
            unfinalized = this;
            //@ ghost seq<Finalizer> newAllocs = seq<Finalizer>{this} + Finalizer.allocs;
            //@ ghost allocs = newAllocs;
        }
    }

    /* Invoked by VM */
    //@ static_level 3;
    //@ requires finalizePre(finalizee) ** Perm(Finalizer.allocs, 1\2);
    //@ ensures Perm(Finalizer.allocs, 1\2);
    static void register(Object finalizee) {
        new Finalizer(finalizee);
    }

    //@ static_level 3;
    //@ requires Perm(Finalizer.allocs, 1\2) ** this \in Finalizer.allocs;
    //@ requires Perm(referent, write) ** finalizePre(referent) ** jla != null;
    //@ ensures Perm(Finalizer.allocs, 1\2) ** !(this \in Finalizer.allocs);
    public void runFinalizer(JavaLangAccess jla) {
        //@ openDupInv Finalizer;

        synchronized (lock) {
            if (this.next == this) { // already finalized
                //@ assert false;
                return;
            }
            // unlink from unfinalized
            if (unfinalized == this) {
                unfinalized = this.next;
                //@ assert allocs[0] == this;
                //@ ghost seq<Finalizer> allocsP = allocs[1 .. ];
                //@ ghost allocs = allocsP;
            } else {
                //@ assert (\exists int i; 0 <= i && i < |allocs|; allocs[i] == this);
                //@ ghost int myIndex = getUnconstrainedInt();
                //@ assume 0 <= myIndex && myIndex < |allocs| && allocs[myIndex] == this;
                //@ ghost seq<Finalizer> allocsBefore = allocs;
                //@ ghost seq<Finalizer> allocsP = allocs[ .. myIndex] + allocs[myIndex + 1 .. ];
                //@ assert |allocsBefore| == |allocsP| + 1;
                //@ assert (\forall int i; 0 <= i && i < myIndex; allocsBefore[i] == allocsP[i]);
                //@ assert (\forall int i; myIndex < i && i < |allocsP|; allocsBefore[i+1] == allocsP[i]);
                //@ ghost allocs = allocsP;
                this.prev.next = this.next;
            }
            if (this.next != null) {
                this.next.prev = this.prev;
            }
            this.prev = null;
            this.next = this;           // mark as finalized
        }

        try {
            Object finalizee = this.get();
            if (finalizee != null) {
                jla.invokeFinalize(finalizee);

                // Clear stack slot containing this variable, to decrease
                // the chances of false retention with a conservative GC
                finalizee = null;
            }
        } catch (Throwable x) { }
        clear();
    }

    /*@
    ghost int getUnconstrainedInt();
    */
}