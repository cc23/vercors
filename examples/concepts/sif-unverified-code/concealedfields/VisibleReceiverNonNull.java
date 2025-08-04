// example will only work with weak/strong preconditions for SIF method invocation:
// for x.method() => weak precondition: low(x != null) instead of strong pre: x != null
package vercors.sif.unverifedcode.examples.concealedfields;

//@ unverified_class
class UnverifiedClass{
    public int field;
    public void unverifiedFunction(Object o);
}

//@ uc_invariant leakable(unverifiedClass) ** low(unverifiedClass) ** unverifiedClass != null;
class VisibleReceiver {
    // conc = {unverifiedClass} --> disallowed!
    // invariant = low(unverifiedClass);

    //@ modifiable
    private UnverifiedClass unverifiedClass;

    //@ requires unverifiedClass != null;
    //@ requires leakable(unverifiedClass);
    //@ ensures hidden(this);
    //@ ensures Perm(this.unverifiedClass, write);
    //@ ensures leakable(this.unverifiedClass);
    //@ ensures this.unverifiedClass == unverifiedClass;
    public VisibleReceiver(UnverifiedClass unverifiedClass) {
        this.unverifiedClass = unverifiedClass;
    }

    //secure!
    // passes 2nd verification since inv = low(unverifiedClass)
    //@ requires lowEvent;
    //@ requires leakable(this);
    //@ requires low(this);
    //@ ensures leakable(this);
    public void implicitLeaker() {
        UnverifiedClass tmp = this.unverifiedClass;
        tmp.unverifiedFunction(null);
    }

    //secure!
    //passes 2nd verification since inv = low(unverifiedClass)
    //@ requires lowEvent;
    //@ requires leakable(this);
    //@ requires low(this);
    //@ ensures leakable(this);
    public void implicitLeakerAssignment() {
        UnverifiedClass tmp = this.unverifiedClass;
        tmp.field = 3;
    }

    //insecure!
    // visibleReceiver.unverifiedClass is no longer concealed. Therefore, assignments need to be lowEvent
    //@ requires lowEvent;
    //@ requires low(unverifiedClass1);
    //@ requires low(unverifiedClass2);
    //@ requires leakable(unverifiedClass1);
    //@ requires leakable(unverifiedClass2);
    public void main(int secret, UnverifiedClass unverifiedClass1, UnverifiedClass unverifiedClass2) {
        UnverifiedClass uc = new UnverifiedClass();
        VisibleReceiver visibleReceiver = new VisibleReceiver(uc);
        //@ assume (Object) visibleReceiver.unverifiedClass != (Object) visibleReceiver;
        //@ assume (Object) unverifiedClass1 != (Object) visibleReceiver;
        //@ assume (Object) unverifiedClass2 != (Object) visibleReceiver;
        //@ leak(visibleReceiver)
        uc.unverifiedFunction(visibleReceiver);
        if (secret == 0) {
            visibleReceiver.unverifiedClass = unverifiedClass1;
        } else {
            visibleReceiver.unverifiedClass = unverifiedClass2;
        }

    }

}
