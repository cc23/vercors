package vercors.sif.unverifedcode.examples.explicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
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

    // secure!
    // @ requires lowEvent;
    public void storeSecretToLeakedObject(int secret) {
        UnverifiedClass uc = new UnverifiedClass();
        DemoClass myObject = new DemoClass();
        //@ leak(myObject)
        uc.unverifiedFunction(myObject);
        myObject.f = 0;
    }
}
