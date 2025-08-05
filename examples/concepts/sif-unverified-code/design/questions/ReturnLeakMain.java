package vercors.sif.unverifedcode.examples.necker.design.questions;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}

//@ uc_invariant low(readable);
class Storage {
    //@ modifiable
    private int readable;

    //@ ensures hidden(this);
    //@ ensures Perm(this.readable, write);
    //@ ensures readable == 0;
    public Storage(){

    }

    //@ requires hidden(this);
    //@ requires Perm(this.readable, write);
    //@ ensures Perm(this.readable, write);
    //@ ensures this.readable == \result;
    //@ ensures hidden(this);
    public int getReadable() {
        return readable;
    }
}

class ReturnLeak {
    // secure
    //@ requires lowEvent;
    public void main(int secret) {
        Storage storage = new Storage();
        storage.readable = secret;

        Storage storage2 = new Storage();

        int tmp = storage.getReadable();
        storage2.readable = tmp;
    }
}