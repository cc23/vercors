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
//@ uc_invariant Perm(unverifiedClass, read) ** leakable(unverifiedClass) ** low(unverifiedClass) ** unverifiedClass != null;
class StoreSecretToLeaked {

    private UnverifiedClass unverifiedClass;

    //@ requires lowEvent;
    //@ ensures hidden(this);
    //@ ensures Perm(unverifiedClass, write);
    //@ ensures leakable(unverifiedClass);
    public StoreSecretToLeaked() {
        this.unverifiedClass = new UnverifiedClass();
    }

    //@ given boolean isLeaked;
    //@ requires lowEvent;
    //@ requires low(this);
    //@ requires low(isLeaked);
    //@ requires isLeaked ==> leakable(this);
    //@ requires !isLeaked ==> hidden(this);
    //@ requires !isLeaked ==> Perm(this.unverifiedClass, write);
    //@ requires !isLeaked ==> low(this.unverifiedClass);
    //@ requires !isLeaked ==> leakable(this.unverifiedClass);
    //@ requires !isLeaked ==> this.unverifiedClass != null;
    //@ ensures !isLeaked ==> Perm(this.unverifiedClass, write);
    //@ ensures !isLeaked ==> hidden(this);
    //@ ensures isLeaked ==> leakable(this);
    //@ ensures leakable(\result) ** low(\result);
    public DemoClass verifiedWrapperMethod(){
        UnverifiedClass tmp = this.unverifiedClass;
        return tmp.unverifiedGetDemoClass();
    }

    //insecure
    //@ requires lowEvent;
    //@ requires low(this);
    //@ requires leakable(this);
    public void verifiedLeakedReturn(int secret){
        DemoClass demoClass = verifiedWrapperMethod() /*@ given {isLeaked=true} @*/;
        demoClass.f = secret;
    }
}
