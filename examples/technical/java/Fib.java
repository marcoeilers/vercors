
// implicit static level 1
class HashMapIntInt {

    // implicit static level 1
    //@ ensures Perm(contents, write);
    //@ ensures contents == map<int,int>{};
    public HashMapIntInt() {};


    //@ ghost map<int, int> contents = map<int,int>{};

    // implicit static level 1
    //@ decreases;
    //@ requires Perm(contents, write);
    //@ ensures Perm(contents, write);
    //@ ensures contents == \old(contents.add(key, value));
    public void put(int key, int value);

    // implicit static level 1
    //@ decreases;
    //@ requires Perm(contents, read);
    //@ requires key \in contents;
    //@ ensures \result == contents[key];
    public /*@ pure @*/ int get(int key);

    // implicit static level 1
    //@ decreases;
    //@ requires Perm(contents, read);
    //@ ensures \result == key \in contents;
    public /*@ pure @*/ boolean containsKey(int key);

}

//@ resource StaticInv()= Perm(Fib.cache, write) ** Perm(Fib.cache.contents, write) ** (0 \in Fib.cache.contents) ** (1 \in Fib.cache.contents) ** (\forall int i; i \in Fib.cache.contents; Fib.cache.contents[i] == Fib.fibSpec(i));

//@ static_level 3;
//@ static_invariant StaticInv();
class Fib {
    private static HashMapIntInt cache;

    // implicit static_level 2;
    static {
        cache = new HashMapIntInt();
        cache.put(0, 1);
        cache.put(1, 1);
        //@ fold StaticInv();
    }

    // implicit static level 1
    public static /*@ pure @*/ int fibSpec(int n){
        if (n <= 1) {
            return 1;
        } else {
            return fibSpec(n - 1) + fibSpec(n - 2);
        }
    }


    // implicit static level 1
    /*@
      requires n >= 0;
      requires StaticInv();
      ensures StaticInv();
      ensures \result == fibSpec(n);
     */
    public static int fib(int n) {
        //@ unfold StaticInv();
        boolean hasKey = cache.containsKey(n);
        if (hasKey) {
            int res = cache.get(n);
            //@ fold StaticInv();
            return res;
        }
        //@ fold StaticInv();
        int result = fib(n - 1) + fib(n - 2);
        //@ unfold StaticInv();
        cache.put(n, result);
        //@ fold StaticInv();
        return result;
    }

    //@ static_level 4;
    public static void main(String[] args) {
        //@ openInv Fib write;
        int fib0 = fib(0);
        int fib1 = fib(1);
        int fib2 = fib(2);
        //@ assert fib2 == Fib.fibSpec(2);
        //@ closeInv Fib write;
        //@ assert fib1 == Fib.fibSpec(1);
        //@ openInv Fib write;
        int fib3 = fib(3);
        //@ assert fib3 == Fib.fibSpec(3);
        int fib4 = fib(4);
    }
}