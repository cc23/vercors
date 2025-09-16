//@ unverified_class
class UnverifiedClass {
    public void unverifiedMethod(Object o);
}

class InternalTimingChannel {

    public int f;

    //@ requires lowEvent;
    //@ requires hidden(this);
    //@ requires Perm(this.f, write);
    public void run2(int secret){
        for(int i = 0; i < secret || secret == -1; i++){
        }
        this.f = secret;
    }
}