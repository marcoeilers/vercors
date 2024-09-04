/*@
  static_level 2;
  static_invariant myNumber >= 33;
@*/
class JavaString {
    public static final String CONST = "my constant string";
    public static final String CONST2 = "my constant string";

    static int myNumber = 0;

    public int intNumber = 0;

    /*@
      requires Perm(myNumber,write);
      static_level 4;
    @*/
    static {
        myNumber = 42;
    }

    /*@
      requires Perm(myNumber,write);
      requires myNumber == 0;
      static_level 5;
    @*/
    public void g() {
        assert myNumber == 0;
        "xuz";
        assert "abc" == "abc";
        // assert "abc".data()[0] != "xyz".data()[0]; // Needed for viper 22.02. Unfortunately spec string doesn't have indexing yet
        assert "abc" != "xyz";

        String xxx;
        String s1 = "aaa";
        String s2 = "bbb";
        String s3 = s1 + s2;

        assert "".isEmpty() || !"".isEmpty();

        //assert CONST != CONST2;
    }

}
