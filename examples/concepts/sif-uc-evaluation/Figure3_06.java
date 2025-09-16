//@ unverified_class
class UnverifiedClass {
    public void callMethod(Object o);
}

class VerifiedClass {

    //@ ensures hidden(this);
    public VerifiedClass() {

    }

    //@ requires lowEvent;
    public void highConstructorCall(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        if(secret > 0){
            new VerifiedClass();
        }
        VerifiedClass obj = new VerifiedClass();
        //@ leak(obj)
        uc.callMethod(obj);
    }
}