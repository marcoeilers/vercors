package hre.unix;

import com.sun.jna.Library;
import com.sun.jna.Native;

public interface LibC extends Library {
    LibC INSTANCE = Native.load(null, LibC.class);

    int getrusage(int who, RUsage usage);
}
