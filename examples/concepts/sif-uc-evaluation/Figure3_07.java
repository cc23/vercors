//@ unverified_class
class UnverifiedClass {
    public void callMethod(int i);
}

class PublicRead {
    //@ modifiable
    private int secretField;
    public int f;

    //@ requires leakable(obj1) ** low(obj1) ** obj1 != null;
    //@ requires leakable(obj2) ** low(obj2) ** obj2 != null;
    //@ requires lowEvent;
    public void highReceiver(PublicRead obj1, PublicRead obj2){
        UnverifiedClass uc = new UnverifiedClass();
        int secret = obj1.secretField;
        PublicRead myObj;
        if(secret > 0){
            myObj = obj1;
        } else {
            myObj = obj2;
        }
        int value = myObj.f;
        uc.callMethod(value);
    }
}