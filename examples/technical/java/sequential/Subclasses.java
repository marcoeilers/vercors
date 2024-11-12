
//@ static_level 2;
//@ static_invariant Perm(A.a, write) ** A.a == 4;
class A {

    static int a;

    //@ static_level 1;
    static {
        B.m(); // rejected because there is a cycle
        a = 4;
    }

}

//@ static_level 7;
//@ static_invariant Perm(A2.a2, write) ** A2.a2 == 4;
class A2 {

    static int a2;

    //@ static_level 6;
    static {
        B.m(); // okay because no cycle
        a2 = 4;
    }

}

// level must be greater than that of C.
//@ static_level 5;
class B extends C {

    //@ decreases;
    //@ static_level 1;
    public static void m(){
        return;
    }
}

//@ static_level 4;
//@ static_invariant Perm(C.c, write) ** C.c == 4;
class C {

    static int c;

    //@ static_level 3;
    static {
        //@ openInv A write;
        int a = A.a;
        c = a;
        //@ closeInv A write;
    }

}