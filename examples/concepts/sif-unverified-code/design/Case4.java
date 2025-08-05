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
    public void case4(int secret) {
        DemoClass leakedObject = new DemoClass();
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        //leak by passing as argument to a method of unverified object
        //@ leak(leakedObject)
        unverifiedClass.unverifiedFunction(leakedObject);
        leakedObject.f = secret;
    }

}