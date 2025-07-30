package vercors.sif.unverifedcode.examples.concealedfields;

// Wir brauchen eine zusätzliche Specification, um zu sagen, dass ein Field nicht exposed wird -> tatsächlich "private" ist.
// Es ist secure secrets in solchen Feldern zu speichern, auch wenn das Objekt Leakable ist.
// es muss also gelten, leakable(this) ==> \forall f : fields, !(f in concealed_fields) ==> low(f)

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}

//@ uc_invariant low(readable);
class Simple {

    //@ ensures hidden(this);
    //@ ensures Perm(this.readable, write);
    //@ ensures Perm(this.notReadable, write);
    public Simple(){

    }

    //invariant low(readable)

    //modifiable_fields=(notReadable, readable)
    //concealed_fields=(notReadable)

    //@ modifiable
    private int notReadable;
    //@ modifiable
    private int readable;

    // secure
    //@ requires leakable(this);
    //@ ensures leakable(this);
    public int getReadable() {
        return readable;
    }

    //@ requires leakable(this);
    //@ ensures leakable(this);
    public void setNotReadable(int i){
        this.notReadable = i;
    }

    //@ requires leakable(this);
    //@ requires low(i) && low(this);
    //@ requires lowEvent;
    //@ ensures leakable(this);
    public void setReadable(int i){
        this.readable = i;
    }

    // insecure
    //@ requires hidden(this) ** Perm(this.notReadable, read);
    //@ ensures hidden(this) ** Perm(this.notReadable, read);
    public int getNotReadable(){
        return notReadable;
    }

    //insecure
    //@ requires leakable(this);
    //@ requires low(i) && low(this);
    //@ requires lowEvent;
    //@ ensures leakable(this);
    // fails 2nd verification because assignment to reabable needs to be lowEvent (also fails 1st verification)
    public void setReadableConditional(int i){
        int tmp = this.notReadable;
        if(tmp > 0){
            this.readable = i;
        }
    }

    //@ requires lowEvent;
    public void main(int secret) {
        Simple myObj = new Simple();
        myObj.notReadable = secret;
        myObj.readable = secret;
        myObj.notReadable = 0;
        myObj.readable = 0;
        //@ leak(myObj)
        UnverifiedClass uc = new UnverifiedClass();
        uc.unverifiedFunction(myObj);
        //secure
        myObj.notReadable = secret;
        //insecure!
        myObj.readable = secret;
    }
}
