package vercors.sif.unverifedcode.examples.concealedfields;
//@ uc_invariant Perm(this.concealedField, read);
class NestedPublicCalls {

    private int concealedField;
    public int readableField;

    // insecure
    // without inv: low(concealedField) 2nd verification fails
    //@ requires leakable(this);
    public int method() {
        int tmp = concealedField;
        return identity(tmp);
    }

    // insecure
    // without inv: low(concealedField) 2nd verification fails, because precondition of leakingWrite doesn't hold
    //@ requires leakable(this);
    //@ requires lowEvent;
    //@ requires low(this);
    public int method2(){
        int tmp = concealedField;
        leakingWrite(tmp);
        return 1;
    }

    //secure
    //@ ensures low(myArg) ==> low(\result);
    public int identity(int myArg) {
        return myArg;
    }

    // secure
    //@ requires low(myArg);
    //@ requires leakable(this);
    //@ requires low(this);
    //@ requires lowEvent;
    public void leakingWrite(int myArg) {
        readableField = myArg;
    }

}
