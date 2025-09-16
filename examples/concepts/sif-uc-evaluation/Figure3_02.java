//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}

//@ uc_invariant true;
class MethodDef {

    //@ modifiable
    private int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
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