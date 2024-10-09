/*@
  static_level 2;
  static_invariant Perm(myNumber, write);
  static_invariant JavaString.myNumber >= 33;
  dup_static_invariant Perm(invonly, read);
  dup_static_invariant JavaString.invonly == 0;
@*/
class JavaString {
    public static final String CONST = "my constant string";
    public static final String CONST2 = "my constant string";

    static int myNumber = 0;
    static int hurgh = 0;

    public int intNumber = 0;
    public int lck = 0;
    public static int invonly = 0;


    /*@
      requires n > 0;
      static_level 5;
    @*/
    public JavaString(int n) {
        intNumber = n;
        //@ commit this;
    }

    /*@
      static_level 4;
    @*/
    static {
        // implicitly: inhale perm to all static fields

        int i = 6;
        //@ decreases i;
        while (i > 0)
        {
            i--;
        }
        myNumber = 42;
        invonly = 0;
    } // implicitly: ensures staticInv, dupStaticInv
      // implicitly: must terminate

    public static void nonTerm() { nonTerm(); }

    /*@
      requires Perm(myNumber,write);
      requires Perm(hurgh, write);
      requires myNumber == 0;
      requires \onInit(JavaString)(Perm(myNumber,write));
      static_level 5;
    @*/
    public void g() {
        JavaString js = new JavaString(5);  // inhale \initialized(JavaString);


        assert myNumber == 0;
        "xuz";
        assert "abc" == "abc";
        // assert "abc".data()[0] != "xyz".data()[0]; // Needed for viper 22.02. Unfortunately spec string doesn't have indexing yet
        assert "abc" != "xyz";

        String xxx;
        String s1 = "aaa";
        String s2 = "bbb";
        String s3 = s1 + s2;

        //@ assert \initialized(Other);
        //@ assert \token(Other, write);

        assert "".isEmpty() || !"".isEmpty();

        //assert CONST != CONST2;
    }

    public static void main(String[] args) {
        // implicit: requires \token(JavaString, write) ** \token(Other, write) ** ...


        //@ assert \token(JavaString, write);
        //@ openDupInv JavaString;
        // openInv JavaString write;
        int asdasd = JavaString.myNumber;

        JavaString.myNumber = 1234567;  // inhale \initialized(JavaString);
    }

    public static void main2(String[] args) {
        // assert \token(JavaString, write);
        int asdasd = 123123123213213;
    }

}


class Other {

    //@ static_level 456;
    static {
        //@ openDupInv JavaString;


        //@ openInv JavaString write;

        JavaString.myNumber = 55; // inhale \initialized(JavaString);

        //@ closeInv JavaString write;
    }
}