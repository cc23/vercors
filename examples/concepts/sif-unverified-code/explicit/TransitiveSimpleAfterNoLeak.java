package vercors.sif.unverifedcode.examples.explicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}

class DemoClass {
    public int f;
    public DemoClass object;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    //@ ensures Perm(this.object, write);
    //@ ensures this.f == 0;
    //@ ensures this.object == null;
    //@ ensures leakable(object);
    public DemoClass() {

    }
}

class Transitive {

    //insecure
    //@ requires lowEvent;
    public void leakSecretObject(int secret) {
        UnverifiedClass uc = new UnverifiedClass();
        DemoClass myObject = new DemoClass();
        DemoClass my2ndLayerObject = new DemoClass();
        //@ assert (Object) myObject != (Object) my2ndLayerObject;
        //@ leak(myObject)
        uc.unverifiedFunction(myObject);
        my2ndLayerObject.f = secret;
        //insecure
        myObject.object = my2ndLayerObject;
    }

}