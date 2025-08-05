//from F.Neckers Master Thesis p.17-18
package vercors.sif.unverifedcode.examples.explicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(int i);
    public void unverifiedFunction(Object o);
}

class EvenHolderInsecure {

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
        this.f = i;
    }

    // insecure
    //@ requires lowEvent;
    public static void main(int secret) {
        UnverifiedClass uc = new UnverifiedClass();
        EvenHolderInsecure ph = new EvenHolderInsecure();
        //@ leak(ph)
        uc.unverifiedFunction(ph);
        int tmp = ph.f;
        if (tmp % 2 != 0) { // could be true
            uc.unverifiedFunction(secret);
        }
    }
}
