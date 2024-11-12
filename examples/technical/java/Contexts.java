// implicit static level 1
class SourceFile {}

// implicit static level 1
class Context {
    private SourceFile _source = null;

    //@ decreases;
    // implicit static_level 1;
    //@ ensures Perm(this._source, write);
    //@ ensures this._source == null;
    public Context() {}

    // implicit static level 1
    //@ requires Perm(this._source, read);
    public final /*@ pure @*/ SourceFile source() {
        return _source;
    }

    // implicit static level 1
    //@ requires Perm(this._source, write);
    //@ ensures Perm(this._source, write);
    //@ ensures this._source == source;
    void setSource(SourceFile source) {
        _source = source;
    }
}

//@ static_level 2;
//@ dup_static_invariant Perm(Contexts.NoContext, read) ** Perm(Contexts.NoContext._source, read);
class Contexts {
    public static final Context NoContext;

    // implicit static_level 1;
    static {
        NoContext = new Context();
    }
}

//@ static_level 5;
//@ dup_static_invariant Perm(Implicits.NoMatchingFailure, read) ** Perm(Implicits.NoMatchingFailure._tag, read) ** Perm(Implicits.NoMatchingFailure._source, read);
class Implicits {
    public static final SearchFailure NoMatchingFailure;

    // implicit static_level 4;
    static {
        //@ openDupInv Contexts;
        Context nc = Contexts.NoContext;
        NoMatchingFailure = new SearchFailure(1, nc.source());
    }
}

// implicit static_level 1;
class SearchFailure {
    private int _tag;
    private SourceFile _source;

    //@ decreases;
    // implicit static_level 1;
    //@ ensures Perm(this._tag, write) ** Perm(this._source, write);
    //@ ensures this._tag == tag;
    //@ ensures this._source == source;
    public SearchFailure(int tag, SourceFile source) {
        this._tag = tag;
        this._source = source;
    }

    // implicit static level 1
    //@ requires Perm(_tag, read);
    public /*@ pure @*/ int tag() {
        return _tag;
    }

    // implicit static level 1
    //@ requires Perm(_source, read);
    public /*@ pure @*/ SourceFile source() {
        return _source;
    }
}