package vercors.sif.unverifedcode.examples.concealedfields;

//@ uc_invariant Perm(concealed, read) ** low(concealed%2);
class NonLowConcealed {

    private int concealed;

    //@ requires low(concealed%2);
    //@ ensures hidden(this);
    //@ ensures Perm(this.concealed, write);
    //@ ensures this.concealed == concealed;
    public NonLowConcealed(int concealed) {
        this.concealed = concealed;
    }

    // fails in 2nd verification! concealed is not modifiable
    //@ requires hidden(this);
    //@ requires Perm(this.concealed, write);
    public void setConcealed(int concealed) {
        this.concealed = concealed;
    }

    //@ requires leakable(this);
    public int checkConcealed() {
        int tmp = concealed;
        return tmp % 2;
    }

    //@ requires lowEvent;
    public void main(int secret) {
        NonLowConcealed obj = new NonLowConcealed(100);
        if (secret < 0) {
            int tmp = obj.concealed;
            tmp -= 10;
            obj.concealed = tmp;
        }
        //leak(obj)
    }

}
