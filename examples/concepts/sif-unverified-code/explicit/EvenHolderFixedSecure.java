//from F.Neckers Master Thesis p.18-19
package vercors.sif.unverifedcode.examples.explicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(int i);
    public void unverifiedFunction(Object o);
}

//@ uc_invariant f%2 == 0;
class EvenHolderSecure {
    //invariant f%2 == 0
    //@ modifiable
    private int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    //@ ensures this.f == 0;
    public EvenHolderInsecure() {

    }

    //@ requires hidden(this);
    //@ requires Perm(this.f, write);
    //@ requires i%2 == 0;
    //@ ensures Perm(this.f, write);
    //@ ensures this.f == i;
    //@ ensures hidden(this);
    public void setF(int i) {
        if (i % 2 == 0) {
            this.f = i;
        }
    }

    // secure
    //@ requires lowEvent;
    public void main(int secret) {
        UnverifiedClass uc = new UnverifiedClass();
        EvenHolderSecure ph = new EvenHolderSecure();
        //@ leak(ph)
        uc.unverifiedFunction(ph);
        int tmp = ph.f;
        if (tmp % 2 != 0) { //always false
            //leak secret
            uc.unverifiedFunction(secret);
        }
    }
}
