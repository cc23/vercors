package vercors.sif.unverifedcode.examples.explicit;

//@ unverified_class
class UnverifiedClass{
    public DemoClass unverifiedGetDemoClass();
}

class DemoClass {
    public int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    //@ ensures this.f == 0;
    public DemoClass() {

    }
}

class StoreSecretToLeaked {

    //insecure
    //@ requires lowEvent;
    public void unverifiedReturn(int secret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        DemoClass myObject = unverifiedClass.unverifiedGetDemoClass();
        myObject.f = secret;
    }

}
