//@ unverified_class
class UnverifiedClass {
    public void callMethod(int i);
}

//@ uc_invariant Perm(this.secretField, read) ** (0 <= secretField && secretField < 2);
class PublicRead {
    private int secretField;
    public int f;

    //@ requires leakable(obj1) ** low(obj1) ** obj1 != null;
    //@ requires leakable(obj2) ** low(obj2) ** obj2 != null;
    //@ requires lowEvent;
    public void highReceiver(PublicRead obj1, PublicRead obj2){
        UnverifiedClass uc = new UnverifiedClass();
        int secret = obj1.secretField;
        PublicRead[] publicReads = new PublicRead[2];
        publicReads[0] = obj1;
        publicReads[1] = obj2;
        PublicRead myObj = publicReads[secret];
        int value = myObj.f;
        //@ declassify(secret)
        uc.callMethod(value);
    }
}