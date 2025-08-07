// Implementation limitation => should NOT verify
package vercors.sif.unverifedcode.examples.implicit;

class DemoClass {
    public void demoMethod(int i) {
        //do nothing
    }
}


class UnverifiedReceiver {

    //insecure! But verifies, because of VerCors not being able to track the runtime class of a object
    //@ requires lowEvent;
    //@ requires hidden(this);
    //@ requires leakable(d1) ** low(d1);
    //@ requires leakable(d2) ** low(d2);
    public void potentialUnverifiedSubclass(DemoClass d1, DemoClass d2, int secret) {
        if (d1 != null && d2 != null) { // needed because of VerCors null receiver check
            DemoClass receiver;
            if (secret > 0) {
                receiver = d1;
            } else {
                receiver = d2;
            }
            receiver.demoMethod(secret);
        }
    }
}
