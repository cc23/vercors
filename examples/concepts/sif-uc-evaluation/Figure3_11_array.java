//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}
//@ uc_invariant Perm(secret, read) ** (0 <= secret && secret < 2);
class PublicWrite {

    public int f;

    private int secret;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write) ** f == 0;
    //@ ensures Perm(this.secret, write) ** secret == 0;
    public PublicWrite() {
    }

    //@ requires lowEvent;
    //@ requires leakable(secretProvider);
    public void highReceiver(PublicWrite secretProvider, int secret){
        UnverifiedClass uc = new UnverifiedClass();
        PublicWrite myObj1 = new PublicWrite();
        //@ assume myObj1 != secretProvider;
        PublicWrite myObj2 = new PublicWrite();
        //@ assume myObj2 != secretProvider;
        PublicWrite[] myObjs = new PublicWrite[2];
        myObjs[0] = myObj1;
        myObjs[1] = myObj2;
        //@ leak(myObj1)
        //@ leak(myObj2)
        uc.unverifiedMethod(myObj1);
        uc.unverifiedMethod(myObj2);
        int secret = secretProvider.secret;
        PublicWrite receiver = myObjs[secret];
        receiver.f = 42;
    }
}