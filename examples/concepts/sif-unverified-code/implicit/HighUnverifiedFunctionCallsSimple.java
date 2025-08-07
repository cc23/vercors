package vercors.sif.unverifedcode.examples.implicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(int i);
}

public class HighUnverifiedFunctionCalls {

    //insecure
    //@ requires lowEvent;
    public void highUnverifiedCall(int secret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        if (secret > 0) {
            unverifiedClass.unverifiedFunction(0);
        }
    }

}
