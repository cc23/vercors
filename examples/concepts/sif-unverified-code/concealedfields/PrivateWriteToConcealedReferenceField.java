package vercors.sif.unverifedcode.examples.concealedfields;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}
class PrivateWriteToConcealedReferenceField {

    //@ requires lowEvent;
    public void main(boolean secret) {
        D d = new D();
        d.field = 2;
        D leakedD = new D();
        leakedD.d = d;
        //@ leak(d)
        //@ leak (leakedD)
        UnverifiedClass uc = new UnverifiedClass();
        uc.unverifiedFunction(leakedD);
    }
}

//@ uc_invariant leakable(dConcealed) ** low(dConcealed);
class D {
    public int field;
    public D d;
    //@ modifiable
    private D dConcealed;

    //@ ensures Perm(this.d, write);
    //@ ensures Perm(this.field, write);
    //@ ensures Perm(this.dConcealed, write);
    //@ ensures hidden(this);
    //@ ensures leakable(this.d);
    //@ ensures leakable(this.dConcealed);
    //@ ensures this.d == null;
    //@ ensures this.dConcealed == null;
    //@ ensures this.field == 0;
    public D() {

    }

    // secure
    //@ requires leakable(this);
    public int getDField() {
        D d = this.d;
        return d.field;
    }

    // secure
    //@ requires leakable(this);
    //@ requires lowEvent;
    //@ requires low(this);
    // -> else this.dConcealed might not be low
    private void concealedToNonConcealed() {
        D dConcealed = this.dConcealed;
        this.d = dConcealed;
    }

    // secure
    // thanks to inv = low(dConcealed), passes 2nd verification
    //@ requires leakable(this);
    //@ requires lowEvent;
    //@ requires low(this);
    public void concealedToNonConcealedPublic() {
        concealedToNonConcealed();
    }
}