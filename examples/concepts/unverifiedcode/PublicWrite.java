//@ uc_invariant this.privF == 2;
class TryThis {

    //@ ensures hidden(this);
    //@ ensures Perm(privF, write);
    //@ ensures Perm(publicF, write);
    //@ ensures privF == 2;
    //@ ensures publicF == 0;
    public TryThis() {
    }

    //@ modifiable
    private int privF = 2;
    public int publicF;

    // last assertion should fail
    //@ requires lowEvent;
    public void test() {
        TryThis t = new TryThis();
        //@ leak(t)
        int y = t.privF;
        assert y == 2;
        t.publicF = 2;
        int z = t.publicF;
        //assert z == 2;
    }

    //@ requires leakable(this);
    // all of the following preconditions are needed
    //@ requires low(this);
    //@ requires lowEvent;
    //@ requires low(i);
    public void setPublicF(int i) {
        publicF = i;
    }

}

