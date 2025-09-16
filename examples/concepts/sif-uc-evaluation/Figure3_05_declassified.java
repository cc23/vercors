//@ unverified_class
class UnverifiedClass {
    public void callMethod();
}

class HighReceiver {

    //@ requires lowEvent;
    public void highReceiver(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        //@ declassify(secret > 0)
        if(secret > 0){
            uc = new UnverifiedClass();
        }
        uc.callMethod();
    }
}