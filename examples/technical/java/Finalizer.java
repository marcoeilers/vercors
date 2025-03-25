
/*@ lock_invariant Perm(Finalizer.unfinalized, write) ** Perm(Finalizer.allocs, 1\2) ** (Finalizer.unfinalized != null ==> (Finalizer.unfinalized \in Finalizer.allocs)) **
                   (\forall* int i, int j; 0 <= i && i < j && j < |Finalizer.allocs|; Finalizer.allocs[i] != Finalizer.allocs[j]) **
                   (\forall* int i; { Finalizer.allocs[i] } 0 <= i && i < |Finalizer.allocs|;
                        Perm(Finalizer.allocs[i].next, write) ** Perm(Finalizer.allocs[i].prev, write) **
                        (Finalizer.allocs[i] != null)) **
                    (\forall* int i; { Finalizer.allocs[i].prev } 0 <= i && i < |Finalizer.allocs|;
                        (Finalizer.allocs[i].prev == (i == 0 ? null : Finalizer.allocs[i - 1]))) **
                    (\forall* int i; { Finalizer.allocs[i].next } 0 <= i && i < |Finalizer.allocs|;
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
                //@ ghost int myIndex = getIndexOf(allocs, this);
                //@ ghost seq<Finalizer> allocsBefore = allocs;
                //@ ghost seq<Finalizer> allocsP = dropElement(allocs, myIndex);
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
    requires (\exists int i; 0 <= i && i < |allocs|; allocs[i] == f);
    ensures 0 <= \result && \result < |allocs| && allocs[\result] == f;
    pure int getIndexOf(seq<Finalizer> allocs, Finalizer f);
    */

    /*@
    requires 0 <= index && index < |allocs|;
    ensures |allocs| == |\result| + 1;
    ensures (\forall int i; { \result[i] } 0 <= i && i < index; allocs[i] == \result[i]);
    ensures (\forall int i; { \result[i] } index < i && i < |\result|; allocs[i+1] == \result[i]);
    pure seq<Finalizer> dropElement(seq<Finalizer> allocs, int index) = allocs[ .. index] + allocs[index + 1 .. ];
     */
}