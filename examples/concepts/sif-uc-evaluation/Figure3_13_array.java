//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}
//@ uc_invariant Perm(secret, read) ** (0 <= secret && secret < 2) ** low(f);
class ModWrite {

    //@ modifiable
    private int f;

    private int secret;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write) ** f == 0;
    //@ ensures Perm(this.secret, write) ** secret == 0;
    public ModWrite() {
    }

    //@ requires lowEvent;
    //@ requires leakable(secretProvider);
    public void highReceiver(ModWrite secretProvider, int secret){
        UnverifiedClass uc = new UnverifiedClass();
        ModWrite myObj1 = new ModWrite();
        //@ assume myObj1 != secretProvider;
        ModWrite myObj2 = new ModWrite();
        //@ assume myObj2 != secretProvider;
        ModWrite[] myObjs = new ModWrite[2];
        myObjs[0] = myObj1;
        myObjs[1] = myObj2;
        //@ leak(myObj1)
        //@ leak(myObj2)
        uc.unverifiedMethod(myObj1);
        uc.unverifiedMethod(myObj2);
        int secret = secretProvider.secret;
        ModWrite receiver = myObjs[secret];
        receiver.f = 42;
    }
}