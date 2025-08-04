package vercors.sif.unverifedcode.examples.concealedfields;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}

//@ uc_invariant low(notReallyConcealed);
class WrongConcealedFields {
    // concealed = {notReallyConcealed} --> disallowed
    // inv = low(notReallyConcealed)
    //@ modifiable
    private int notReallyConcealed;

    //@ ensures hidden(this);
    //@ ensures Perm(this.notReallyConcealed, write);
    //@ ensures this.notReallyConcealed == 0;
    public WrongConcealedFields(){

    }

    //secure!
    //@ requires Perm(this.notReallyConcealed, read);
    //@ requires hidden(this);
    //@ ensures Perm(this.notReallyConcealed, read);
    //@ ensures \result == this.notReallyConcealed;
    public int getNotReallyConcealed() {
        return notReallyConcealed;
    }

    // insecure!
    // wrongConcealedFields.notReallyConcealed is no longer concealed. Therefore, assignments need to be lowEvent
    //@ requires lowEvent;
    private void main(boolean secret) {
        WrongConcealedFields wrongConcealedFields = new WrongConcealedFields();
        UnverifiedClass unverifiedClass = new UnverifiedClass();
        //@ leak(wrongConcealedFields)
        unverifiedClass.unverifiedFunction(wrongConcealedFields);
        if (secret) {
            wrongConcealedFields.notReallyConcealed = 4;
        }
    }
}

// ==> transformed after new viper encoding into:
//
//class WrongConcealedFieldsEncoded {
//    // concealed = {notReallyConcealed} --> not allowed!
//    // inv = low(notReallyConcealed)
//
//    private int notReallyConcealed;
//
//    // requires Perm(this.notReallyConcealed, read);
//    // ensures Perm(this.notReallyConcealed, read);
//    // ensures \result == this.notReallyConcealed;
//    public int getNotReallyConcealed_h() {
//        return notReallyConcealed;
//    }
//
//    // ensures low(\result);
//    // ensures Perm(leakable(\result)) > 0;
//    public int getNotReallyConcealed_l() {
//        //assume low(this)
//        //inhale (leakable(this), write)
//        //from invariant learn: low(notReallyConcealed) -> verifies
//        return notReallyConcealed;
//    }
//}