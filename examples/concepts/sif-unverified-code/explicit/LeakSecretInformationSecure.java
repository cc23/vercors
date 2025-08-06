package vercors.sif.unverifedcode.examples.explicit;


//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}

class DemoClass {
    public int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    public DemoClass() {

    }
}

class LeakSecretInformation {

    //secure
    //@ requires lowEvent;
    public void dontLeakSecretObject(int secret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        DemoClass myObject = new DemoClass();
        myObject.f = secret;
        myObject.f = 0;
        //@ leak(myObject)
        unverifiedClass.unverifiedFunction(myObject);
    }

}
