package vercors.sif.unverifedcode.examples.concealedfields;

//@ uc_invariant true;
class SetConcealedAndLeak {
    // mod = {concealedField}
    //@ modifiable
    private int concealedField;

    //insecure -> race condition with adversarial code
    // fails 2nd verification, as from this.concealedField = concealedField follows only inv = true and not low(this.concealedField)
    //@ requires hidden(this);
    //@ requires Perm(this.concealedField, write);
    public int setConcealedField(int concealedField) {
        this.concealedField = concealedField;
        return this.concealedField;
    }

    //secure
    //@ requires hidden(this);
    //@ requires Perm(this.concealedField, write);
    public int setConcealedFieldSecure(int concealedField) {
        this.concealedField = concealedField;
        return concealedField;
    }

    //secure
    //@ requires hidden(this) ** Perm(this.concealedField, write);
    //@ ensures hidden(this) ** Perm(this.concealedField, write);
    //@ ensures \result == concealedField && this.concealedField == concealedField;
    private int setConcealedFieldPriv(int concealedField) {
        this.concealedField = concealedField;
        return this.concealedField;
    }

    //secure
    //@ requires leakable(this);
    //@ ensures leakable(this);
    private int setConcealedFieldPrivLeakable(int concealedField) {
        this.concealedField = concealedField;
        return this.concealedField;
    }

    //insecure
    // 2nd verification fails, as precondition hidden(this) is not met -> try with leakable method
    //@ requires hidden(this) ** Perm(this.concealedField, write);
    //@ ensures hidden(this) ** Perm(this.concealedField, write);
    public int setConcealedFieldViaMethodCall(int concealedField) {
        setConcealedFieldPriv(concealedField);
        return this.concealedField;
    }

    //insecure
    // 2nd verification fails, as postcondition of setConcealedFieldPriv is not strong enough to prove low(\result)
    //@ requires leakable(this);
    //@ ensures leakable(this);
    public int setConcealedFieldViaMethodCallLeakable(int concealedField) {
        setConcealedFieldPrivLeakable(concealedField);
        return this.concealedField;
    }
}
