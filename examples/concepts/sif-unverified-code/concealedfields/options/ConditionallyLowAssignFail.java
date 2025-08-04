package vercors.sif.unverifedcode.examples.concealedfields.options;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(int o);
}

//@ uc_invariant low(flag) && (flag ==> low(concealedField));
class ConditionallyLowAssignFail {
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
    //@ requires low(this);
    //@ requires Perm(this.flag, write);
    //@ requires Perm(this.concealedField, write);
    //@ requires low(this.concealedField);
    //@ requires low(flag);
    //@ requires lowEvent;
    //@ ensures hidden(this);
    //@ ensures Perm(this.flag, write);
    //@ ensures Perm(this.concealedField, write);
    private void setFlag(boolean flag) {
        this.flag = flag;
    }

    // not secure!
    // fails, since between the two assignments the adversary could set this.flag to false, and we would lose the guarantee low(concealedField)
    //@ requires hidden(this);
    //@ requires Perm(this.flag, write);
    //@ requires Perm(this.concealedField, write);
    //@ requires low(concealedField);
    //@ requires low(this);
    //@ requires lowEvent;
    //@ ensures Perm(this.flag, write);
    //@ ensures Perm(this.concealedField, write);
    //@ ensures this.concealedField == concealedField;
    //@ ensures this.flag;
    public void setConcealedFieldLow(int concealedField) {
        this.concealedField = concealedField;
        this.flag = true;
    }

    //@ requires hidden(this);
    //@ requires Perm(this.flag, write);
    //@ requires Perm(this.concealedField, write);
    //@ requires lowEvent;
    //@ ensures Perm(this.concealedField, write);
    //@ ensures Perm(this.flag, write);
    //@ ensures this.concealedField == concealedField;
    //@ ensures !this.flag;
    public void setConcealedFieldHigh(int concealedField) {
        this.flag = false;
        this.concealedField = concealedField;
    }

    // not secure!
    //@ requires lowEvent;
    public void main(int secret) {
        ConditionallyLowAssignFail myObj = new ConditionallyLowAssignFail();
        if(secret > 0){
            myObj.concealedField = 3;
        }
        //passes, as conditionallyLowAssign is hidden -> inv doesnt need to hold
        myObj.flag = true;
        //fails, since conditionallyLowAssingFail.concealedField is not low
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        int tmp = myObj.concealedField;
        unverifiedClass.unverifiedFunction(tmp);
    }
}
