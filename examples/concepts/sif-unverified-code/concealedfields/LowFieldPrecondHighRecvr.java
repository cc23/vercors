//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction();
}

//@ uc_invariant true;
class CounterExample {

    private boolean f;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    //@ ensures this.f == f;
    public CounterExample(boolean f){
        this.f = f;
    }

    //@ requires Perm(this.f, read) ** low(this.f);
    //@ requires hidden(this);
    //@ requires lowEvent;
    //@ ensures hidden(this);
    private void myMethod(){
        boolean tmp = this.f;
        UnverifiedClass uc = new UnverifiedClass();
        if(tmp){
            uc.unverifiedFunction();
        }
    }

    //@ requires lowEvent;
    public void main(boolean secret){
        CounterExample c1 = new CounterExample(true);
        CounterExample c2 = new CounterExample(false);
        //@ assert low(c1.f);
        //@ assert low(c2.f);
        CounterExample cHigh;

        if(secret){
            cHigh = c1;
        } else {
            cHigh = c2;
        }
        // insecure since low(cHigh.f) does not hold
        cHigh.myMethod();
    }
}