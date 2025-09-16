//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}

//@ uc_invariant low(this.f);
class ModWrite {

    //@ modifiable
    private int f;

    //@ requires leakable(this);
    public int getF(){
        return this.f;
    }

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write) ** f == 0;
    public ModWrite() {
    }

    //@ requires lowEvent;
    public void highEvent(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        ModWrite myObj = new ModWrite();
        //@ leak(myObj)
        uc.unverifiedMethod(myObj);
        if(secret > 0){
            myObj.f = 42;
        }
    }
}