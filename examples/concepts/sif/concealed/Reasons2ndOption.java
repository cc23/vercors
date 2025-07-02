
class Incompleteness2ndOption {

    private int concealedField;

    /*@ requires Perm(this.concealedField, write);
        requires low(concealedField);
        ensures Perm(this.concealedField, write);
        ensures this.concealedField == concealedField;
    @*/
    public void setConcealedField(int concealedField) {
        this.concealedField = concealedField;
        //@ assert low(this.concealedField);
    }

    //not secure! invariant is not established after call
    public void main(int secret) {
        Incompleteness2ndOption incompleteness2ndOption = new Incompleteness2ndOption();
        if (secret == 0) {
            incompleteness2ndOption.setConcealedField(0);
        }
    }
}
