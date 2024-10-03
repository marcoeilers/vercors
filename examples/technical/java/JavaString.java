/*@
  static_level 2;
  static_invariant Perm(myNumber, write);
  static_invariant JavaString.myNumber >= 33;
  dup_static_invariant Perm(myNumber, write);
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
      requires n > 456;
      static_level 5;
    @*/
    public JavaString(int n) {
        intNumber = n;
    }

    /*@
      static_level 4;
    @*/
    static {
        int i = 6;
        // decreases i;
        while (i > 0)
        {
            i--;
        }
        nonTerm();
        myNumber = 42;
    }

    public static void nonTerm() { nonTerm(); }

    /*@
      requires Perm(myNumber,write);
      requires Perm(hurgh, write);
      requires myNumber == 0;
      requires \onInit(JavaString)(Perm(myNumber,write));
      static_level 5;
    @*/
    public void g() {
        JavaString js = new JavaString(5);


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

}


class Other {

    //@ static_level 456;
    static {
        //@ openDupInv JavaString;
        //@ openInv JavaString write;
        JavaString.myNumber = 55;
        //@ closeInv JavaString write;
        //JavaString.myNumber = 55;
    }
}