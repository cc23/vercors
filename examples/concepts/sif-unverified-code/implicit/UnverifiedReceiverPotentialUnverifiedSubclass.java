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
    //@ requires hidden(demoClass);
    //@ requires low(demoClass);
    public void potentialUnverifiedSubclass(DemoClass demoClass, int secret) {
        if (demoClass != null) { // needed because of VerCors null receiver check
            demoClass.demoMethod(secret);
        }
    }
}
