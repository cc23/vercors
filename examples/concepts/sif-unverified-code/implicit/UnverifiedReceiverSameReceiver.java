package vercors.sif.unverifedcode.examples.implicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedCall();
}


class UnverifiedReceiver {

    //secure!
    // (method needs to be private because of VerCors Null Receiver check before function calls)
    //@ requires lowEvent;
    //@ requires hidden(this);
    //@ requires leakable(unverifiedObj1) ** low(unverifiedObj1) ** unverifiedObj1 != null;
    //@ requires leakable(unverifiedObj2) ** low(unverifiedObj2) ** unverifiedObj2 != null;
    private void sameReceiver(UnverifiedClass unverifiedObj1, UnverifiedClass unverifiedObj2, int secret) {
        UnverifiedClass receiver;
        if (secret > 0) {
            receiver = unverifiedObj1;
        } else {
            receiver = unverifiedObj2;
        }
        if (unverifiedObj1 == unverifiedObj2) {
            receiver.unverifiedCall();
        }
    }
}
