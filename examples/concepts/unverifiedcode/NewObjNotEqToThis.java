package vercors.sif.unverifedcode.examples.concealedfields;

class TryThis {

    //@ ensures hidden(this);
    public TryThis() {

    }

    //@ requires lowEvent;
    public void main() {
        TryThis t = new TryThis();
        //@ assert this != t;
        //@ assert perm(leakable(t)) == 0;
    }

}