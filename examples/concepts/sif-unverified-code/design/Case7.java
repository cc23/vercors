package vercors.sif.unverifedcode.examples.necker.design;
//@ unverified_class
class UnverifiedContainer{
    public DemoClass item;
}

class DemoClass {
    public Object object;
    public int f;

    //@ ensures Perm(this.f, write);
    //@ ensures Perm(this.object, write);
    //@ ensures this.f == 0;
    //@ ensures this.object == null;
    //@ ensures hidden(this);
    //@ ensures leakable(this.object);
    public DemoClass() {

    }
}
//@ uc_invariant Perm(unverifiedContainer, read) ** leakable(unverifiedContainer) ** low(unverifiedContainer);
class LeakSecretByCases {

    private UnverifiedContainer unverifiedContainer;

    //insecure
    //@ requires lowEvent;
    //@ requires leakable(this);
    //@ ensures leakable(this);
    public void case7(int secret) {
        //leakedObject gotten from public field of an unverified object
        UnverifiedContainer tmp = this.unverifiedContainer;
        DemoClass leakedObject = unverifiedContainer.item;
        leakedObject.f = secret;
    }
}