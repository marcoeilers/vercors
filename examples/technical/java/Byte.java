/*@
  static_level 1;
  dup_static_invariant Perm(Byte.cache, read) ** Byte.cache != null ** Byte.cache.length == 256;
  dup_static_invariant (\forall* int i ; 0 <= i && i < Byte.cache.length ; Perm(Byte.cache[i], read));
  dup_static_invariant (\forall* int i, int j; 0 <= i && i < Byte.cache.length && i < j && j < Byte.cache.length ; Byte.cache[i] != Byte.cache[j]);
  dup_static_invariant (\forall* int i ; 0 <= i && i < Byte.cache.length ; Perm(Byte.cache[i].value, read) ** Byte.cache[i].value == i-128 );
@*/
class Byte {
    byte value;
    final static Byte[] cache;

    //@ decreases;
    //@ ensures Perm(this.value, write) ** this.value == value;
    public Byte(byte value) {
        this.value = value;
    }

    static {
        cache = new Byte[256];
        //@ loop_invariant 0 <= i && i <= 256 ** Perm(Byte.cache, read) ** Byte.cache != null ** Byte.cache.length == 256;
        //@ loop_invariant (\forall* int j ; 0 <= j && j < Byte.cache.length ; (Perm(Byte.cache[j], write)));
        //@ loop_invariant (\forall* int k, int j; 0 <= k && k < i && k < j && j < i ; Byte.cache[k] != Byte.cache[j]);
        //@ loop_invariant (\forall* int j ; 0 <= j && j < i ; (Perm(Byte.cache[j].value, write) ** Byte.cache[j].value == (j - 128)));
        //@ decreases 256 - i;
        for(int i = 0; i < cache.length; i++){
            cache[i] = new Byte((byte)(i - 128));
        }
    }

    /*@
    static_level 2;
    requires -128 <= b && b <= 127;
    ensures \result!=null ** Perm(\result.value, read) ** \result.value == b;
    @*/
    public static Byte valueOf(byte b) {
        final int offset = 128;
        Byte js = new Byte(5);  // inhale \initialized(Byte);

        //@ openDupInv Byte;
        return Byte.cache[(int)b + offset];
    }
}