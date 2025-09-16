//@ unverified_class
class UnverifiedClass {
    public void callMethod(int i);
}

class Explicit {

    //@ requires lowEvent;
    public void explicit(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        uc.callMethod(secret);
    }
}