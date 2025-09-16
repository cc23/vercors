//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}

class LeakOperation {

    public int f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write) ** f == 0;
    public LeakOperation() {
    }

    //@ requires lowEvent;
    public void highEvent(int secret){
        UnverifiedClass uc = new UnverifiedClass();
        LeakOperation myObj = new LeakOperation();
        myObj.f = secret;
        //@ leak(myObj)
        uc.unverifiedMethod(myObj);
    }
}