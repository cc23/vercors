//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}

//@ uc_invariant low(this.f);
class MethodDef {

    //@ modifiable
    private int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    //@ ensures this.f == 0;
    public MethodDef() {

    }
    //@ requires hidden(this) ** Perm(this.f, read);
    public int getF() {
        return this.f;
    }

    //@ requires lowEvent;
    public void emptyInvariant(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        MethodDef myObj = new MethodDef();
        //@ leak(myObj)
        uc.unverifiedMethod(myObj);
        myObj.f = secret;
    }
}