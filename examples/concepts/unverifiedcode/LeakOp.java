//@ uc_invariant this.privF == 2;
class TryThis {

    //@ ensures hidden(this);
    //@ ensures Perm(privF, write);
    //@ ensures Perm(t, write);
    //@ ensures Perm(publicF, write);
    //@ ensures privF == 2;
    //@ ensures low(t);
    //@ ensures publicF == 0;
    //@ ensures leakable(t);
    public TryThis() {
    }

    //@ modifiable
    private int privF = 2;
    public int publicF;
    public TryThis t;

    //@ requires lowEvent;
    public void test() {
        TryThis t = new TryThis();
        //@ leak(t)
        int y = t.privF;
        int z = t.publicF;
        assert y == 2;
    }

}

