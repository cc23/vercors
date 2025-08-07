package vercors.sif.unverifedcode.examples.implicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}

class DemoClass{
    private int f;

    //@ ensures hidden(this);
    public DemoClass(int f){
        this.f = f;
    }
}

class HighUnverifiedFunctionCalls {

    //insecure!
    //@ requires lowEvent;
    public void differentObjects(int secret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        DemoClass obj1 = new DemoClass(0);
        DemoClass obj2 = new DemoClass(0);
        //@ leak(obj1)
        //@ leak(obj2)
        DemoClass argForCall;
        if(secret > 0){
            argForCall = obj1;
        } else {
            argForCall = obj2;
        }
        unverifiedClass.unverifiedFunction(argForCall);
    }

}
