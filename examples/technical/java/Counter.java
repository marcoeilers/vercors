/*@
	static_level 7;
	dup_static_invariant Perm(Counter.max, read) **
		0 < Counter.max;
	dup_static_invariant Perm(Counter.lock, read) **
		Counter.lock != null    **
		committed(Counter.lock);
@*/
class Counter {
    final static int max = 10000;
    static int count;
    private static Lock lock;
    //@ ghost static map<int, Location> nonces;

    static {
        count = 0;
        lock = new Lock();
        // trying to call the constructor below to an error:
        // "Key not found: constructor"
        // NonceDispenser nd = new NonceDispenser();
        NonceDispenser nd = allocNonces();
        //@ ghost nonces = nd.nonces;
        //@ fold StaticInv();
        //@ commit lock;
    }

    //@ ensures Perm(Counter.nonces, read);
    //@ ensures Perm(Counter.max, read);
    //@ ensures \result < Counter.max ==> Nonce(Counter.nonces, \result);
    //@ static_level 7;
    public static int getAndInc() {
        //@ openDupInv Counter;
        int r = Counter.max;
        synchronized (lock) {
            //@ unfold StaticInv();
            if (count < Counter.max) {
                r = Counter.count;
                Counter.count++;
            }
            //@ fold StaticInv();
        }
        return r;
    }

    //@ static_level 6;
    //@ requires Perm(Counter.max, read) ** Counter.max == 10000;
    //@ ensures  Perm(\result.nonces, write);
    //@ ensures (\forall* int i; 0 <= i && i < 10000; Nonce(\result.nonces, i));
    //@ decreases;
    public NonceDispenser allocNonces() {
        NonceDispenser nd = new NonceDispenser();
        //@ ghost map<int, Location> nonces = map<int, Location>{};

        //@ loop_invariant Perm(Counter.max, read) ** Counter.max == 10000;
        //@ loop_invariant 0 <= i && i <= 10001;
        //@ loop_invariant (\forall* int j; 0 <= j && j < i; Nonce(nonces, j));
        //@ loop_invariant (\forall int j; true; (j \in nonces.keys) == (0 <= j && j < i));
        //@ decreases 10001 - i;
        for (int i = 0; i <= 10000; i++) {
            Location l = new Location();
            //@ ghost map<int, Location> newd = nonces.add(i, l);
            //@ fold Nonce(newd, i);
            //@ loop_invariant newd == nonces.add(i, l);
            //@ loop_invariant !(i \in nonces.keys);
            //@ loop_invariant (\forall* int j; k <= j && j < i; Nonce(nonces, j));
            //@ loop_invariant (\forall* int j; 0 <= j && j < k; Nonce(newd, j));
            //@ decreases i - k;
            for (int k = 0; k < i; k++) {
                //@ unfold Nonce(nonces, k);
                //@ fold Nonce(newd, k);
            }
            //@ ghost nonces = newd;
        }
        //@ ghost nd.nonces = nonces;
        return nd;
    }



    //@ static_level 8;
    static void test() {
        int i = Counter.getAndInc();
        int j = Counter.getAndInc();
        if (i < Counter.max && j < Counter.max) {
            //@ assert Perm(Counter.nonces, read);
            //@ assert Nonce(Counter.nonces, i);
            //@ assert Nonce(Counter.nonces, j);
            // The following call leads to an error:
            // Counter.noncesAreUnique(i, j);
            // We inline the body here instead:
            //@ unfold Nonce(Counter.nonces, i);
            //@ unfold Nonce(Counter.nonces, j);
            //@ assert Counter.nonces[i] != Counter.nonces[j];
            //@ fold Nonce(Counter.nonces, i);
            //@ fold Nonce(Counter.nonces, j);
            //@ assert i != j;
        }
    }

    //@ requires Perm(Counter.nonces, read);
    //@ requires Nonce(Counter.nonces, i);
    //@ requires Nonce(Counter.nonces, j);
    //@ ensures  Perm(Counter.nonces, read);
    //@ ensures  Nonce(Counter.nonces, i);
    //@ ensures  Nonce(Counter.nonces, j);
    //@ ensures  i != j;
    //@ static_level 6;
    public static noncesAreUnique(int i, int j) {
        //@ unfold Nonce(Counter.nonces, i);
        //@ unfold Nonce(Counter.nonces, j);
        //@ assert Counter.nonces[i] != Counter.nonces[j];
        //@ fold Nonce(Counter.nonces, i);
        //@ fold Nonce(Counter.nonces, j);
    }
}

/*@
resource StaticInv() =
	Perm(Counter.count, write) **
	(0 <= Counter.count)       **
	Perm(Counter.max, read)    **
	Perm(Counter.nonces, read) **
	(\forall* int i; Counter.count <= i && i < Counter.max; Nonce(Counter.nonces, i));
@*/

//@ static_level 5;
//@ lock_invariant StaticInv();
class Lock {}


class Location{
    int l;
};


class NonceDispenser {
    //@ ghost map<int, Location> nonces;
}

/*@
resource Nonce(map<int, Location> nonceDispenser, int n) =
	0 <= n **
	Perm(Counter.max, read)   **
	n <= Counter.max          **
	n \in nonceDispenser.keys **
	Perm(nonceDispenser[n].l, write);
@*/
