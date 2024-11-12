

class HashMapIntInt {

    //@ ensures Perm(contents, write);
    //@ ensures contents == map<int,int>{};
    public HashMapIntInt() {};


    //@ ghost map<int, int> contents = map<int,int>{};

    //@ decreases;
    //@ requires Perm(contents, write);
    //@ ensures Perm(contents, write);
    //@ ensures contents == \old(contents.add(key, value));
    public void put(int key, int value);

    //@ decreases;
    //@ requires Perm(contents, read);
    //@ requires key \in contents;
    //@ ensures \result == contents[key];
    public /*@ pure @*/ int get(int key);

    //@ decreases;
    //@ requires Perm(contents, read);
    //@ ensures \result == key \in contents;
    public /*@ pure @*/ boolean containsKey(int key);

}

//@ resource StaticInv()= Perm(ConcFib.cache, write) ** Perm(ConcFib.cache.contents, write) ** (0 \in ConcFib.cache.contents) ** (1 \in ConcFib.cache.contents) ** (\forall int i; i \in ConcFib.cache.contents; ConcFib.cache.contents[i] == ConcFib.fibSpec(i));

//@ lock_invariant StaticInv();
class ConcFibLock {}


//@ static_level 3;
//@ dup_static_invariant Perm(ConcFib.lock, read) ** ConcFib.lock != null ** committed(ConcFib.lock);
class ConcFib {
    private static HashMapIntInt cache;
    private static ConcFibLock lock;

    //@ static_level 2;
    static {
        cache = new HashMapIntInt();
        cache.put(0, 1);
        cache.put(1, 1);
        //@ fold StaticInv();
        lock = new ConcFibLock();
        //@ commit lock;
    }

    public static /*@ pure @*/ int fibSpec(int n){
        if (n <= 1) {
            return 1;
        } else {
            return fibSpec(n - 1) + fibSpec(n - 2);
        }
    }



    /*@
      static_level 5;
      requires n >= 0;
      ensures \result == fibSpec(n);
     */
    public static int fib(int n) {
        //@ openDupInv ConcFib;
        synchronized (lock) {
            //@ unfold StaticInv();
            boolean hasKey = cache.containsKey(n);
            if (hasKey) {
                int res = cache.get(n);
                //@ fold StaticInv();
                return res;
            }
            //@ fold StaticInv();
        }
        int result = fib(n - 1) + fib(n - 2);
        synchronized (lock) {
            //@ unfold StaticInv();
            cache.put(n, result);
            //@ fold StaticInv();
        }

        return result;
    }

    //@ static_level 10;
    public static void main(String[] args) {
        int fib0 = fib(0);
        int fib1 = fib(1);
        int fib2 = fib(2);
        //@ assert fib2 == ConcFib.fibSpec(2);
        //@ assert fib1 == ConcFib.fibSpec(1);
        int fib3 = fib(3);
        //@ assert fib3 == ConcFib.fibSpec(3);
        int fib4 = fib(4);
    }
}