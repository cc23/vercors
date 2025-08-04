package vercors.sif.unverifedcode.examples.concealedfields;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}

class MyContainer {
    public int content;
}

class VisibleEventAssignment {
    // conc = {value}
    //@ modifiable
    private int value;
    public MyContainer container;

    //@ ensures hidden(this);
    //@ ensures Perm(this.value, write);
    //@ ensures Perm(this.container, write);
    //@ ensures this.container == null;
    //@ ensures leakable(this.container);
    public VisibleEventAssignment() {

    }

    //insecure!
    //@ requires hidden(this);
    //@ requires Perm(this.container, read) ** Perm(this.value, read);
    //@ requires low(this.value);
    //@ requires low(this.container);
    //@ requires lowEvent;
    //@ requires leakable(this.container);
    //@ ensures hidden(this);
    //@ ensures Perm(this.container, read) ** Perm(this.value, read);
    // following precondition is only needed because of a problem VerCors has -> fix it!
    // fails 2nd verification, as assignments to container.content need to be lowEvent, but low(this.value) doesn't hold

    // -> see unverifiedcode/VerCorsFailPredsDiffTypedObjs.java
    //@ requires (Object) this.container != (Object) this;
    public void implicitLeakerEvent() {
        int tmp = this.value;
        MyContainer contTmp = this.container;
        if (tmp == 0) {
            contTmp.content = 0;
        } else {
            contTmp.content = 1;
        }
    }

    //secure!
    //@ requires lowEvent;
    public void main(int secret) {
        VisibleEventAssignment myObj = new VisibleEventAssignment();
        UnverifiedClass uc = new UnverifiedClass();
        //@ leak(myObj)
        uc.unverifiedFunction(myObj);
        myObj.value = 1;

        if (secret == 1) {
            myObj.value = 0;
        }
    }
}
