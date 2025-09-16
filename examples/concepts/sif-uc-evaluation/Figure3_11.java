//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}

class PublicWrite {

    public int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write) ** f == 0;
    public PublicWrite() {
    }

    //@ requires lowEvent;
    public void highReceiver(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        PublicWrite myObj1 = new PublicWrite();
        PublicWrite myObj2 = new PublicWrite();
        //@ leak(myObj1)
        //@ leak(myObj2)
        uc.unverifiedMethod(myObj1);
        uc.unverifiedMethod(myObj2);
        PublicWrite receiver;
        if(secret > 0){
            receiver = myObj1;
        } else {
            receiver = myObj2;
        }
        receiver.f = 42;
    }
}