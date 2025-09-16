//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}

//@ uc_invariant Perm(this.f, read) ** low(this.f);
class LeakOperation {

    private int f;

    //@ requires leakable(this);
    public int getF(){
        return this.f;
    }

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write) ** f == 0;
    public LeakOperation() {
    }

    //@ requires lowEvent;
    public void highEvent(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        LeakOperation myObj = new LeakOperation();
        myObj.f = secret;
        //@ declassify(secret)
        //@ leak(myObj)
        uc.unverifiedMethod(myObj);
    }
}