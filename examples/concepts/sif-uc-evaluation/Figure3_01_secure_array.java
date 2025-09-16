//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o1, Object o2) {};
}

//@ uc_invariant low(f) ** Perm(secret, read) ** (0 <= secret && secret < 2);
class RelInv {

    private int secret;
    //@ modifiable
    private int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    //@ ensures Perm(this.secret, write);
    //@ ensures this.f == 0;
    //@ ensures secret == 0;
    public RelInv() {
    }

    //@ requires lowEvent;
    //@ requires leakable(secretProvider);
    public void emptyInvariant(RelInv secretProvider){
        UnverifiedClass uc = new UnverifiedClass();
        RelInv obj1 = new RelInv();
        obj1.f = 1;
        //@ assume obj1 != secretProvider;
        RelInv obj2 = new RelInv();
        obj1.f = 2;
        //@ assume obj2 != secretProvider;
        //@ leak (obj1)
        //@ leak (obj2)
        uc.unverifiedMethod(obj1, obj2);
        RelInv[] myArray = new RelInv[2];
        myArray[0] = obj1;
        myArray[1] = obj2;
        int secret = secretProvider.secret;
        RelInv highObj = myArray[secret];
    }
}