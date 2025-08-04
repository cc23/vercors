package vercors.sif.unverifedcode.examples.concealedfields.options;


//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(int o);
    public void unverifiedFunction(Object o);
}

//@ uc_invariant low(flag) && (flag ==> low(concealedField));
class ConditionallyLowAssignObservation {
    // conc = {concealedField, flag}
    // mod = {concealedField, flag}
    // inv = low(flag) && flag ==> low(concealedField)
    //@ modifiable
    private int concealedField;
    //@ modifiable
    private boolean flag;

    //@ ensures hidden(this);
    //@ ensures Perm(this.flag, write);
    //@ ensures Perm(this.concealedField, write);
    //@ ensures this.flag == false;
    //@ ensures this.concealedField == 0;
    public ConditionallyLowAssignFail() {

    }

    //@ requires hidden(this);
    //@ requires Perm(this.flag, write);
    //@ ensures hidden(this);
    //@ ensures Perm(this.flag, write);
    //@ ensures this.flag == flag;
    private void setFlag(boolean flag) {
        this.flag = flag;
    }

    //@ requires leakable(this);
    //@ requires low(this);
    //@ requires lowEvent;
    //@ requires flag == false;
    //@ ensures leakable(this);
    private void setFlagLeakable(boolean flag) {
        this.flag = flag;
    }

    //@ requires leakable(this);
    //@ requires lowEvent;
    //@ requires low(this);
    //@ requires low(concealedField);
    //@ ensures leakable(this);
    public void setConcealedField(int concealedField) {
        this.concealedField = concealedField;
    }

    // insecure!
    // OBSERVATION: assignments to fields that are only "conditionally low" still need to be lowEvent!
    //@ requires lowEvent;
    public void main(int secret) {
        ConditionallyLowAssignObservation conditionallyLowAssign = new ConditionallyLowAssignObservation();
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        conditionallyLowAssign.setFlag(true);
        conditionallyLowAssign.setFlag(false);
        conditionallyLowAssign.concealedField = secret;
        //@ leak(conditionallyLowAssign)
        unverifiedClass.unverifiedFunction(conditionallyLowAssign);
        //after leak, can only assign false to flag and low values to concealedField
        conditionallyLowAssign.setFlagLeakable(false);

        if(secret > 0){
            conditionallyLowAssign.setConcealedField(3);
        }
    }

    // secure!
    // OBSERVATION: assignments to fields that are only "conditionally low" still need to be lowEvent!
    //@ requires lowEvent;
    public void mainSecure(int secret) {
        ConditionallyLowAssignObservation conditionallyLowAssign = new ConditionallyLowAssignObservation();
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        conditionallyLowAssign.setFlag(true);
        conditionallyLowAssign.setFlag(false);
        conditionallyLowAssign.concealedField = secret;
        //@ leak(conditionallyLowAssign)
        unverifiedClass.unverifiedFunction(conditionallyLowAssign);
        //after leak, can only assign false to flag and low values to concealedField
        conditionallyLowAssign.setFlagLeakable(false);

        conditionallyLowAssign.setConcealedField(3);
    }
}
