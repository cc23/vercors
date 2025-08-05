package vercors.sif.unverifedcode.examples.necker.design;
//@ unverified_class
class UnverifiedContainer{
    public DemoClass getItem();
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
//@ uc_invariant Perm(unverifiedContainer, read) ** leakable(unverifiedContainer) ** low(unverifiedContainer) ** unverifiedContainer != null;
class LeakSecretByCases {

    private UnverifiedContainer unverifiedContainer;

    //@ ensures Perm(unverifiedContainer, write);
    //@ ensures leakable(unverifiedContainer);
    //@ ensures hidden(this);
    //@ ensures unverifiedContainer != null;
    public LeakSecretByCases() {
        unverifiedContainer = new UnverifiedContainer();
    }

    //insecure
    //@ requires lowEvent;
    //@ requires leakable(this);
    //@ ensures leakable(this);
    public void case6(int secret) {
        //leakedObject returned by unverified Method
        UnverifiedContainer tmp = this.unverifiedContainer;
        DemoClass leakedObject = tmp.getItem();
        leakedObject.f = secret;
    }
}