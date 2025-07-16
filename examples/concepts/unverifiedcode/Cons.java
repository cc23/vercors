class Cons {

    private int f;

    // ensures low(this); //we have this directly in the encoding
    public Cons() {
        this.f = 0;
    }
    //@ requires Perm(t.f, write);
    //@ ensures Perm(t.f, write);
    private Cons(int f, Cons t) {
        this.f = f;
        t.f = f;
    }

    //@ requires Perm(t.f, read);
    //@ ensures Perm(t.f, read);
    public Cons(Cons t) {
        this.f = 3;
        //TODO needs field read encodings to work (no permissions in 2nd method verification)
        //this.f = t.f;
    }


    public void f() {
        Cons t = new Cons();
        //@ assert low(t);
    }
}