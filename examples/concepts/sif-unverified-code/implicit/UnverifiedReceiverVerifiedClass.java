// Implementation limitation => cant specify needed precondition
package vercors.sif.unverifedcode.examples.implicit;

class DemoClass {
    public void demoMethod(int i) {
        //do nothing
    }
}


class UnverifiedReceiver {

    //secure!
    //@ requires lowEvent;
    //@ requires hidden(demoClass);
    //@ requires low(demoClass);
    // VerCors does not support this precondition which would be needed:
    //  requires demoClass.getClass() == DemoClass.class
    public void verifiedSubclass(DemoClass demoClass, int secret) {
        if (demoClass != null) { // needed because of VerCors null receiver check
            demoClass.demoMethod(secret);
        }
    }
}
