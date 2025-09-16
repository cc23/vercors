//@ unverified_class
class UnverifiedClass {
    public void callMethod();
}

//@ uc_invariant Perm(this.secret, read) ** (0 <= secret && secret < 2);
class HighReceiver {

    private int secret;

    //@ requires lowEvent;
    //@ requires leakable(secretProvider);
    public void highReceiver(HighReceiver secretProvider) {
        UnverifiedClass[] ucArr = new UnverifiedClass[2];
        ucArr[0] = new UnverifiedClass();
        ucArr[1] = new UnverifiedClass();
        int secret = secretProvider.secret;
        UnverifiedClass uc = ucArr[secret];
        uc.callMethod();
    }
}