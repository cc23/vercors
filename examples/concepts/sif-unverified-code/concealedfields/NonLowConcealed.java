package vercors.sif.unverifedcode.examples.concealedfields;

//@ uc_invariant low(concealed%2);
class NonLowConcealed {

    //@ modifiable
    private int concealed;

    //@ requires leakable(this);
    //@ requires lowEvent && low(this) && low(concealed%2);
    public void setConcealed(int concealed) {
        this.concealed = concealed;
    }

    //@ requires leakable(this);
    public int checkConcealed() {
        int tmp = concealed;
        return tmp % 2;
    }

    //@ requires leakable(nonLowConcealed);
    //@ requires lowEvent;
    //@ requires low(nonLowConcealed);
    public void main(NonLowConcealed nonLowConcealed, int secret) {
        //not secure! nonLowConcealed.concealed could be changed directly after tmp -= 10;
        if (secret < 0) {
            int tmp = nonLowConcealed.concealed;
            tmp -= 10;
            nonLowConcealed.concealed = tmp;
        }
        //not secure!
        if (secret > 0) {
            nonLowConcealed.concealed = 100;
        }
    }

}
