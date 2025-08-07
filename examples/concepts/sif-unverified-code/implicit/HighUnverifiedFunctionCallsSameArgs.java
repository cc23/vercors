package vercors.sif.unverifedcode.examples.implicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(int i);
}

public class HighUnverifiedFunctionCalls {

    //secure but disallowed (incomplete of IFS product program)
    //@ requires lowEvent;
    public void sameArgs(int secret) {
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        if (secret > 0) {
            unverifiedClass.unverifiedFunction(0);
        } else {
            unverifiedClass.unverifiedFunction(0);
        }
    }

}
