//@ unverified_class
class UnverifiedClass {
    public void callMethod();
}

class HighReceiver {
    //@ given boolean indirectlyFromUc;
    //@ requires lowEvent;
    //@ requires 0 <= secret && secret < 2;
    public void highReceiver(int secret){
        UnverifiedClass[] ucArr = new UnverifiedClass[2];
        ucArr[0] = new UnverifiedClass();
        ucArr[1] = new UnverifiedClass();
        //@ assert !indirectlyFromUc ==> 0 <= secret && secret < 2;
        //@ assert !(0 <= secret && secret < 2) ==> (low(secret) && low(ucArr));
        //@ assume 0 <= secret && secret < 2;
        UnverifiedClass uc = ucArr[secret];
        //@ declassify(uc)
        uc.callMethod();
    }
}