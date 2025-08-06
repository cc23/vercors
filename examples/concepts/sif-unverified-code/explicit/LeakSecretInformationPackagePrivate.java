package vercors.sif.unverifedcode.examples.explicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}

class DemoClass {
    int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    public DemoClass() {

    }
}

class LeakSecretInformation {

    //insecure
    //@ requires lowEvent;
    public void leakSecretObject(int secret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        DemoClass myObject = new DemoClass();
        myObject.f = secret;
        //@ leak(myObject)
        unverifiedClass.unverifiedFunction(myObject);
    }

}
