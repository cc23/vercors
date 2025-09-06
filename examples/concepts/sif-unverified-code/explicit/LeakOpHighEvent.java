//@ unverified_class
class UnverifiedClass{
    public void unverifiedMethod(Object i);
}
//@ uc_invariant low(this.privF);
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

    //@ requires lowEvent;
    public void test(int secret) {
        UnverifiedClass uc = new UnverifiedClass();
        TryThis t = new TryThis();
        if(secret > 0){
            t.publicF = 0;
            t.privF = 0;
        } else {
            t.publicF = 1;
            t.privF = 1;
        }
        if(secret > 0){
            //@ leak(t)
        } else {
            //@ leak(t)
        }

        uc.unverifiedMethod(t);
    }

}

