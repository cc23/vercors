package vercors.sif.unverifedcode.examples.explicit;

public class AdversaryCreatedSubclass {
    //@ requires lowEvent;
    public void main(int secret) {
        VerifiedClass unverifiedClass = new UnverifiedClass();
        // Implementation limitation: should fail as the runtime class should be used to decide which encoding to take
        // here the unverified encoding should be used -> fail because secret is not low
        unverifiedClass.storeSecret(unverifiedClass, secret);
    }
}

class VerifiedClass {
    //@ modifiable
    private int concealedField;

    //secure
    //@ requires leakable(verifiedClass);
    //@ ensures leakable(verifiedClass);
    public void storeSecret(VerifiedClass verifiedClass, int secret){
        // even if the runtime class of verifiedClass is unverified this doesnt leak anything
        verifiedClass.concealedField = secret;
    }
}

//@ unverified_class
class UnverifiedClass extends VerifiedClass {

    public int concealedField;

//    Override
//    public void storeSecret(VerifiedClass verifiedClass, int secret){
//        concealedField = secret;
//    }
}
