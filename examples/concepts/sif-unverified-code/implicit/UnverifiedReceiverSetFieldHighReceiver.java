package vercors.sif.unverifedcode.examples.implicit;

//@ unverified_class
class UnverifiedClass {
    public int field;
}


class UnverifiedReceiver {

    //insecure
    //@ requires lowEvent;
    public void setFieldSecure(int secret) {
        UnverifiedClass unverifiedObj1 = new UnverifiedClass();
        UnverifiedClass unverifiedObj2 = new UnverifiedClass();
        UnverifiedClass receiver;
        if (secret > 0) {
            receiver = unverifiedObj1;
        } else {
            receiver = unverifiedObj2;
        }
        receiver.field = 3;
    }
}
