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
        ModWrite myObj1 = new ModWrite();
        ModWrite myObj2 = new ModWrite();
        //@ leak(myObj1)
        //@ leak(myObj2)
        uc.unverifiedMethod(myObj1);
        uc.unverifiedMethod(myObj2);
        ModWrite receiver;
        if(secret > 0){
            receiver = myObj1;
        } else {
            receiver = myObj2;
        }
        receiver.f = 42;
    }
}