package vercors.sif.unverifedcode.examples.necker.design;
class DemoClass{
    public int f;
}

//@ uc_invariant Perm(this.demoClass, read) ** leakable(demoClass) ** low(demoClass);
class LeakSecretByCases {
    // invariant: low(demoClass) && leakable(demoClass)
    // -> needed s.t. getter passes 2nd verification
    private DemoClass demoClass;

    //@ requires leakable(this);
    //@ ensures leakable(this);
    public DemoClass getDemoClass() {
        return demoClass;
    }

    //@ requires leakable(this);
    //@ ensures leakable(this);
    public void case1(int secret) {
        //demoClass is leaked through the getDemoClass method
        DemoClass tmp = this.demoClass;
        tmp.f = secret;
    }
}