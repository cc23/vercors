package vercors.sif.unverifedcode.examples.necker.design;
//@ unverified_class
class UnverifiedClass{
    public Object ref;
}

class DemoClass {

    public int f;

    //@ ensures Perm(this.f, write);
    //@ ensures this.f == 0;
    //@ ensures hidden(this);
    public DemoClass(){

    }
}

class LeakSecretByCases {

    //insecure
    public void case2(int secret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass(); // adv. spawns new thread in constructor
        DemoClass leakedObject = new DemoClass();
        //@ leak(leakedObject)
        //leak by assigning to public field of unverified object
        unverifiedClass.ref = leakedObject;
        leakedObject.f = secret;
    }
}