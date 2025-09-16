//@ unverified_class
class UnverifiedClass {
    public void callMethod(int i);
}

//@ uc_invariant Perm(this.secretField, read) ** (0 <= secretField && secretField < 2) ** Perm(this.f, read) ** low(this.f);
class ModRead {

    private int secretField;
    private int f;

    //@ requires leakable(obj1) ** low(obj1) ** obj1 != null;
    //@ requires leakable(obj2) ** low(obj2) ** obj2 != null;
    //@ requires lowEvent;
    public void highReceiver(ModRead obj1, ModRead obj2){
        UnverifiedClass uc = new UnverifiedClass();
        int secret = obj1.secretField;
        ModRead[] modReads = new ModRead[2];
        modReads[0] = obj1;
        modReads[1] = obj2;
        ModRead myObj = modReads[secret];
        int value = myObj.f;
        uc.callMethod(value);
    }
}