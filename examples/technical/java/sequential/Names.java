// implicit static_level 1;
class Name {
    private final int _start;
    private final int _length;

    //@ decreases;
    // implicit static_level 0;
    //@ ensures Perm(this._start, write) ** Perm(this._length, write);
    //@ ensures this._start == start;
    //@ ensures this._length == length;
    public Name(int start, int length) {
        this._start = start;
        this._length = length;
    }

    //@ requires Perm(this._start, read);
    public /*@ pure @*/ int start() {
        return _start;
    }

    //@ requires Perm(this._length, read);
    public /*@ pure @*/ int length() {
        return _length;
    }
}

//@ static_level 2;
//@ static_invariant Perm(Names.chrs, write) ** Names.chrs != null ** Names.chrs.length == 131072;
//@ static_invariant (\forall* int i ; 0 <= i && i < Names.chrs.length ; Perm(Names.chrs[i], write));
class Names {
    public static final static String[] chrs;

    // implicit static_level 1;
    static {
        chrs = new String[131072];
    }

    //@ decreases;
    //@ static_level 3;
    //@ ensures Perm(\result._start, write) ** Perm(\result._length, write) ** \result._start == 0;
    public static Name nameAlt(String s) {
        //@ openInv Names write;
        Name newName = new Name(0, chrs.length);
        chrs[0] = "a";  // symbolic modification of the array, not doing anything real of course.
        //@ closeInv Names write;
        return newName;
    }


    //@ decreases;
    //@ static_level 2;
    //@ requires Perm(Names.chrs, write) ** Names.chrs != null ** Names.chrs.length > 0 ** Perm(Names.chrs[0], write);
    //@ ensures Perm(Names.chrs, write) ** Names.chrs == \old(Names.chrs) ** Perm(Names.chrs[0], write);
    //@ ensures Perm(\result._start, write) ** Perm(\result._length, write) ** \result._start == 0 ** \result._length == chrs.length;
    //@ ensures Names.chrs[0] == "a";
    public static Name name(String s) {
        Name newName = new Name(0, chrs.length);
        chrs[0] = "a";  // symbolic modification of the array, not doing anything real of course.
        return newName;
    }
}

//@ static_level 4;
//@ dup_static_invariant Perm(StdNames.AnyRef, read) ** Perm(StdNames.Array, read) ** Perm(StdNames.List, read);
//@ dup_static_invariant Perm(StdNames.AnyRef._start, read) ** Perm(StdNames.AnyRef._length, read);
//@ dup_static_invariant Perm(StdNames.Array._start, read) ** Perm(StdNames.Array._length, read);
//@ dup_static_invariant Perm(StdNames.List._start, read) ** Perm(StdNames.List._length, read);
class StdNames {
    public static final Name AnyRef;
    public static final Name Array;
    public static final Name List;

    // implicit static_level 3;
    static {
        //@ openInv Names write;
        AnyRef = Names.name("AnyRef");
        Array = Names.name("Array");
        List = Names.name("List");
        //@ closeInv Names write;
    }
}

// Alternative version that does not acquire the invariant of Names in the initializer of StdNames, but in the
// implementation of Names.name (nameAlt).

//@ static_level 5;
//@ dup_static_invariant Perm(StdNamesAlt.AnyRef, read) ** Perm(StdNamesAlt.Array, read) ** Perm(StdNamesAlt.List, read);
//@ dup_static_invariant Perm(StdNamesAlt.AnyRef._start, read) ** Perm(StdNamesAlt.AnyRef._length, read);
//@ dup_static_invariant Perm(StdNamesAlt.Array._start, read) ** Perm(StdNamesAlt.Array._length, read);
//@ dup_static_invariant Perm(StdNamesAlt.List._start, read) ** Perm(StdNamesAlt.List._length, read);
class StdNamesAlt {
    public static final Name AnyRef;
    public static final Name Array;
    public static final Name List;

    // implicit static_level 4;
    static {
        AnyRef = Names.nameAlt("AnyRef");
        Array = Names.nameAlt("Array");
        List = Names.nameAlt("List");
    }
}