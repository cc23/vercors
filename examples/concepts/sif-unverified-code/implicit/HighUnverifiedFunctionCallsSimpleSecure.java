package vercors.sif.unverifedcode.examples.implicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(int i);
}

public class HighUnverifiedFunctionCalls {

    //secure
    //@ requires lowEvent;
    //@ requires low(noSecret);
    public void highUnverifiedCall(int noSecret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        if (noSecret > 0) {
            unverifiedClass.unverifiedFunction(0);
        }
    }

}
