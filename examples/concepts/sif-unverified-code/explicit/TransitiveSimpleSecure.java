package vercors.sif.unverifedcode.examples.explicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}
//@ uc_invariant Perm(this.object, write);
class DemoClass {
    public int f;
    private DemoClass object;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    //@ ensures Perm(this.object, write);
    //@ ensures this.f == 0;
    //@ ensures this.object == null;
    //@ ensures leakable(object);
    public DemoClass() {

    }

    //secure, since DemoClass.object is private
    //@ requires lowEvent;
    public void leakSecretObject(int secret) {
        UnverifiedClass uc = new UnverifiedClass();
        DemoClass myObject = new DemoClass();
        DemoClass my2ndLayerObject = new DemoClass();
        myObject.object = my2ndLayerObject;
        //@ assert (Object) myObject != (Object) my2ndLayerObject;
        //@ leak(myObject)
        uc.unverifiedFunction(myObject);
        my2ndLayerObject.f = secret;
    }
}