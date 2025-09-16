//@ unverified_class
class UnverifiedClass {
    public void callMethod();
}

class HighEvent {

    //@ requires lowEvent;
    public void highEvent(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        //@ declassify(secret > 0)
        if(secret > 0){
            uc.callMethod();
        }
    }
}