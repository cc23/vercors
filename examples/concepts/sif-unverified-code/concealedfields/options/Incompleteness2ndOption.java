package vercors.sif.unverifedcode.examples.concealedfields.options;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(int o);
    public void unverifiedFunction(Object o);
}

//@ uc_invariant Perm(flag, read) ** low(flag) ** (flag ==> low(concealedField));
class Incompleteness2ndOption {
    // conc = {concealedField, flag}
    // mod = {concealedField}
    // inv = perm(flag, read) && low(flag) && (flag ==> low(concealedField))
    //@ modifiable
    private int concealedField;
    private boolean flag;

    //@ ensures Perm(flag, write);
    //@ ensures Perm(concealedField, write);
    //@ ensures hidden(this);
    //@ ensures flag == false;
    //@ ensures concealedField == 0;
    public Incompleteness2ndOption() {

    }

    //@ requires leakable(this);
    //@ ensures leakable(this);
    public int getConcealedFieldLeakable() {
        boolean tmp = flag;
        if(!tmp){
            return -1;
        }
        return concealedField;
    }

    //@ requires hidden(this);
    //@ requires Perm(this.flag, read);
    //@ requires Perm(this.concealedField, read);
    //@ ensures hidden(this);
    //@ ensures Perm(this.flag, read);
    //@ ensures Perm(this.concealedField, read);
    //@ ensures this.flag ==> \result == concealedField;
    //@ ensures !this.flag ==> \result == -1;
    public int getConcealedField() {
        boolean tmp = flag;
        if(!tmp){
            return -1;
        }
        return concealedField;
    }

    //@ requires leakable(this);
    //@ requires Perm(this.flag, read);
    //@ requires this.flag ==> (low(concealedField) && low(this) && lowEvent);
    //@ ensures leakable(this);
    //@ ensures Perm(this.flag, read);
    public void setConcealedFieldLeakable(int concealedField) {
        this.concealedField = concealedField;
    }

    //@ requires hidden(this);
    //@ requires Perm(this.concealedField, write);
    //@ ensures Perm(this.concealedField, write);
    //@ ensures this.concealedField == concealedField;
    //@ ensures hidden(this);
    public void setConcealedFieldHidden(int concealedField) {
        this.concealedField = concealedField;
    }

    //not secure!
    //@ requires lowEvent;
    public void main(int secret) {
        Incompleteness2ndOption incompleteness2ndOption = new Incompleteness2ndOption();
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        incompleteness2ndOption.flag = false;
        if (secret == 3) {
            incompleteness2ndOption.concealedField = 15;
        }
        //@ leak(incompleteness2ndOption)
        unverifiedClass.unverifiedFunction(incompleteness2ndOption);
        int tmpConcealedField = incompleteness2ndOption.concealedField;
        // high branch, since flag is false
        if (tmpConcealedField > 0) {
            unverifiedClass.unverifiedFunction(1);
        }
    }

    //secure!
    //@ requires lowEvent;
    public void mainSecure(int secret) {
        Incompleteness2ndOption incompleteness2ndOption = new Incompleteness2ndOption();
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        incompleteness2ndOption.flag = false;
        if (secret == 3) {
            incompleteness2ndOption.concealedField = 15;
        }
        //@ leak(incompleteness2ndOption)
        unverifiedClass.unverifiedFunction(incompleteness2ndOption);
        boolean tmpFlag = incompleteness2ndOption.flag;
        int tmpConcealedField = incompleteness2ndOption.concealedField;
        // low branch, since flag is false
        if (tmpFlag && tmpConcealedField > 0) {
            unverifiedClass.unverifiedFunction(1);
        }
    }
}
