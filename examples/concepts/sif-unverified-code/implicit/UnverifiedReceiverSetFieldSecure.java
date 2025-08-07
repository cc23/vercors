package vercors.sif.unverifedcode.examples.implicit;

//@ unverified_class
class UnverifiedClass{
    public int field;
}


class UnverifiedReceiver {

    //secure!
    //@ requires lowEvent;
    public void setFieldSecure(int secret) {
        UnverifiedClass unverifiedObj = new UnverifiedClass();
        unverifiedObj.field = 3;
    }
}
