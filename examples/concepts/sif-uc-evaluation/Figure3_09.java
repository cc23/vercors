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
    public void highValue(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        PublicWrite myObj = new PublicWrite();
        //@ leak(myObj)
        uc.unverifiedMethod(myObj);
        myObj.f = secret;
    }
}