package vercors.sif.unverifedcode.examples.necker.design;

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

//@ uc_invariant Perm(this.demoClass, read) ** leakable(demoClass) ** low(demoClass);
class LeakSecretByCases {

    private DemoClass demoClass;

    //@ requires leakable(this);
    //@ ensures leakable(this);
    public DemoClass getDemoClass() {
        return demoClass;
    }

    //@ requires leakable(this);
    //@ requires Perm(this.demoClass, read);
    //@ requires leakable(this);
    public void case3(int secret) {
        //leak by assigning to public field of a leaked (by case 1) object
        DemoClass tmp = this.demoClass;
        DemoClass leakedObject = new DemoClass();
        //@ leak(leakedObject)
        tmp.object = leakedObject;
        leakedObject.f = secret;
    }

}