package vercors.sif.unverifedcode.examples.necker.design;
//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
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

class LeakSecretByCases {

    //insecure
    //@ requires lowEvent;
    public void case5(int secret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        DemoClass leakedObject = new DemoClass();
        DemoClass helper = new DemoClass();
        helper.object = leakedObject;
        //@ leak(leakedObject)
        //@ leak(helper)
        //leakedObject indirectly leaked
        unverifiedClass.unverifiedFunction(helper);
        leakedObject.f = secret;
    }

}