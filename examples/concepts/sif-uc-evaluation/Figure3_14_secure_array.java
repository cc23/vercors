//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}

//@ uc_invariant Perm(fCopy, read) ** fCopy == f ** low(f) ** Perm(secret, read) ** (0 <= secret && secret < 2);
class ModWrite {

    private int secret;
    private int fCopy;
    //@ modifiable
    private int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    //@ ensures Perm(this.secret, write);
    //@ ensures Perm(this.fCopy, write);
    //@ ensures this.f == f;
    //@ ensures this.fCopy == f;
    //@ ensures secret == 0;
    public ModWrite(int f) {
        this.f = f;
        this.fCopy = f;
    }

    //@ requires hidden(this) ** Perm(this.f, read);
    public int getF() {
        return this.f;
    }

    //@ requires lowEvent;
    //@ requires leakable(secretProvider);
    public void highReceiver(ModWrite secretProvider){
        UnverifiedClass uc = new UnverifiedClass();
        ModWrite myObj1 = new ModWrite(1);
        //@ assume myObj1 != secretProvider;
        ModWrite myObj2 = new ModWrite(2);
        //@ assume myObj2 != secretProvider;
        ModWrite[] myArray = new ModWrite[2];
        myArray[0] = myObj1;
        myArray[1] = myObj2;
        //@ leak (myObj1)
        //@ leak (myObj2)
        uc.unverifiedMethod(myObj1);
        uc.unverifiedMethod(myObj2);
        int secret = secretProvider.secret;
        ModWrite receiver = myArray[secret];
        int fValue = receiver.fCopy;
        receiver.f = fValue;
    }
}