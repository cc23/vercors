package vercors.sif.unverifedcode.examples.concealedfields;


//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
    public void unverifiedFunction(int o);
}

//@ uc_invariant true;
class VisibleEvent {
    // conc = {value}
    //@ modifiable
    private int value;

    //@ ensures hidden(this);
    //@ ensures Perm(this.value, write);
    public VisibleEvent() {

    }

    //insecure!
    //@ requires hidden(this);
    //@ requires Perm(this.value, read) ** low(this.value);
    //@ requires lowEvent;
    //@ ensures hidden(this);
    //@ ensures Perm(this.value, read);
    // fails 2nd verification, as low(this.value) doesn't hold (since it's not part of invariant)
    public void implicitLeaker(){
        int tmp = this.value;
        if (tmp == 0){
            UnverifiedClass uc = new UnverifiedClass();
            uc.unverifiedFunction(1);
        }
    }

    //secure!
    //@ requires lowEvent;
    public void main(int secret){
        VisibleEvent event = new VisibleEvent();
        UnverifiedClass uc = new UnverifiedClass();
        //@ leak(event)
        uc.unverifiedFunction(event);
        event.value = 1;

        if(secret == 1){
            event.value = 0;
        }
    }

//    //but if we would allow the function implicitLeaker function the following adv. code could get information about secret
//    public static AtomicBoolean unverifiedFunctionCalled = new AtomicBoolean(false);
//
//    public static void adversarialCode(VisibleEvent event){
//        new Thread(() -> {
//            event.implicitLeaker();
//            if(unverifiedFunctionCalled.get()){
//                System.out.println("secret == 1");
//            }
//        })
//                .start();
//    }
//    public static void unverifiedFunctionImpl(int i){
//        if(i == 1){
//            unverifiedFunctionCalled.getAndSet(true);
//        }
//    }

}
