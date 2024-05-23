package vct.examples.technical.javabip;

import org.javabip.annotations.*;
import org.javabip.api.PortType;


/*[/expect bipComponentInvariantNotEstablished:false]*/
@ComponentType(initial = INIT, name = NAME)
@StatePredicate(state = "xyz", expr = "true")
@Invariant("false")
@Port(name = GO, type = PortType.enforceable)
public class GuardIsUsed {
    public static final String INIT = "initialState";
    public static final String NAME = "oneComponentOneTransition";
    public static final String GO = "go";
    public static final String GEQ_Y = "greaterEqualY";

    GuardIsUsed() {

    }

    @Pure
    /*[/expect bipGuardPreconditionUnsatisfiable]*/
    @Guard(name = GEQ_Y)
    /*[/end]*/
    public boolean geqZero() {
        return true;
    }
}
/*[/end]*/
