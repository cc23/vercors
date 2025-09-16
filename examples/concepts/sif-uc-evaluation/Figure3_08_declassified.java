//@ unverified_class
class UnverifiedClass {
    public void callMethod(int i);
}

//@ uc_invariant low(this.f);
class ModRead {

    //@ modifiable
    private int secretField;
    //@ modifiable
    private int f;

    //@ requires leakable(obj1) ** low(obj1) ** obj1 != null;
    //@ requires leakable(obj2) ** low(obj2) ** obj2 != null;
    //@ requires lowEvent;
    public void highReceiver(ModRead obj1, ModRead obj2){
        UnverifiedClass uc = new UnverifiedClass();
        int secret = obj1.secretField;
        ModRead myObj;
        //@ declassify(secret > 0)
        if(secret > 0){
            myObj = obj1;
        } else {
            myObj = obj2;
        }
        int value = myObj.f;
        uc.callMethod(value);
    }
}