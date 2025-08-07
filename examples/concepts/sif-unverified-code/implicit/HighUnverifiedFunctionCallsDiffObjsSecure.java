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

    //secure!
    //@ requires lowEvent;
    //@ requires low(noSecret);
    public void differentObjects(int noSecret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        DemoClass obj1 = new DemoClass(0);
        DemoClass obj2 = new DemoClass(0);
        DemoClass argForCall;
        if(noSecret > 0){
            argForCall = obj1;
        } else {
            argForCall = obj2;
        }
        //@ leak(argForCall)
        unverifiedClass.unverifiedFunction(argForCall);
    }

}
