package vercors.sif.unverifedcode.examples.concealedfields;

// Wir brauchen eine zusätzliche Specification, um zu sagen, dass ein Field nicht exposed wird -> tatsächlich "private" ist.
// Es ist secure secrets in solchen Feldern zu speichern, auch wenn das Objekt Leakable ist.
// es muss also gelten, leakable(this) ==> \forall f : fields, !(f in concealed_fields) ==> low(f)

//@ unverified_class
class UnverifiedClass{
    public void unverifiedMethod(Object o);
}
//@ uc_invariant low(readable);
class Complex {

    //modifiable_fields=(notReadable, readable)
    //concealed_fields=(notReadable)

    //inv: low(readable)

    //@ modifiable
    private int notReadable;
    //@ modifiable
    private int readable;

    //@ ensures hidden(this);
    //@ ensures Perm(this.readable, write);
    //@ ensures Perm(this.notReadable, write);
    public Complex() {

    }
    // secure
    //@ requires hidden(this);
    //@ requires Perm(this.readable, read);
    //@ ensures Perm(this.readable, read) ** \result == this.readable;
    public int getReadable() {
        return readable;
    }

    // secure
    //@ requires leakable(this);
    //@ requires Perm(this.readable, read);
    //@ ensures Perm(this.readable, read) ** \result == this.readable;
    public int getReadableLeakable() {
        return readable;
    }

    //@ requires hidden(this);
    //@ requires Perm(this.notReadable, write);
    //@ ensures Perm(this.notReadable, write) ** this.notReadable == i;
    public void setNotReadable(int i){
        this.notReadable = i;
    }

    //@ requires hidden(this);
    //@ requires Perm(this.readable, write) ** low(i);
    //@ ensures Perm(this.readable, write) ** this.readable == i ** low(this.readable);
    public void setReadable(int i){
        this.readable = i;
    }

    // insecure
    //@ requires hidden(this);
    //@ requires Perm(this.notReadable, read);
    //@ ensures Perm(this.notReadable, read) ** \result == this.notReadable;
    public int getNotReadable(){
        return notReadable;
    }

    //@ requires lowEvent;
    public void main(int secret) {
        Complex myObj = new Complex();
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        myObj.notReadable = secret;
        myObj.readable = secret;
        myObj.notReadable = 0;
        myObj.readable = 0;
        //@ leak(myObj)
        unverifiedClass.unverifiedMethod(myObj);
        //secure
        myObj.notReadable = secret;
        //insecure!
        myObj.readable = secret;
    }
}
