//TODO fix
package vercors.sif.unverifedcode.examples.concealedfields;

//@ unverified_class
class UnverifiedClass{
    public int field;
    public void unverifiedFunction(Object o);
}

//@ uc_invariant leakable(unverifiedClass) ** low(unverifiedClass);
class VisibleReceiver {
    // conc = {unverifiedClass} --> disallowed!
    // invariant = low(unverifiedClass);

    //@ modifiable
    private UnverifiedClass unverifiedClass;

    //@ requires leakable(unverifiedClass);
    //@ requires low(unverifiedClass);
    //@ ensures hidden(this);
    //@ ensures Perm(this.unverifiedClass, write);
    //@ ensures leakable(this.unverifiedClass);
    //@ ensures this.unverifiedClass == unverifiedClass;
    public VisibleReceiver(UnverifiedClass unverifiedClass) {
        this.unverifiedClass = unverifiedClass;
    }


    //secure!
    //passes 2nd verification since inv = low(unverifiedClass)
    //@ requires leakable(this);
    //@ requires low(this);
    //@ requires lowEvent;
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
