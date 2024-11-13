//@ resource P();
//@ resource Q();


class Literal {}

class Theory {
    //@ static_level 3;
    //@ requires P();
    //@ ensures Q();
    public void actualAssertLiteral(Literal l);

    // generic contract for assertLiteral
    //@ static_level 3;
    //@ requires P();
    //@ ensures Q();
    public void assertLiteral(Literal l);
}

//@ static_level 2;
//@ dup_static_invariant Perm(LATheory.version, read) ** LATheory.version != null;
class LATheory extends Theory {
    static String version;

    static {
        version = "Version 3";
    }

    //@ static_level 3;
    // identical contract guarantees behavioral subtyping (though this is currently not checked by Vercors).
    //@ requires P();
    //@ ensures Q();
    public void assertLiteral(Literal l) {
        //@ openDupInv LATheory;

        // some operation that requires well-definedness of version:
        //@ assert version != null;

        // Workaround to be able to call the method from the superclass (Vercors does not support direct call).
        Theory t = this;
        t.actualAssertLiteral(l);
    }
}

//@ static_level 2;
//@ static_invariant Perm(NLATheory.nClauses, write) ** NLATheory.nClauses >= 0;
class NLATheory extends Theory {
    static int nClauses;

    static {
        nClauses = 0;
    }

    //@ static_level 3;
    // identical contract guarantees behavioral subtyping (though this is currently not checked by Vercors).
    //@ requires P();
    //@ ensures Q();
    public void assertLiteral(Literal l) {
        //@ openInv NLATheory write;
        int newClause = nClauses;
        nClauses++;
        //@ closeInv NLATheory write;

        // some operation that requires well-definedness of nClauses:
        //@ assert newClause >= 0;

        // Workaround to be able to call the method from the superclass (Vercors does not support direct call).
        Theory t = this;
        t.actualAssertLiteral(l);
    }
}