package vercors.sif.unverifedcode.examples.implicit;

//@ unverified_class
class UnverifiedClass{
    public int field;
}


class UnverifiedReceiver {

    //insecure
    //@ requires lowEvent;
    public void setFieldSecure(int secret) {
        UnverifiedClass unverifiedObj = new UnverifiedClass();
        if (secret > 0) {
            unverifiedObj.field = 3;
        }
    }
}
