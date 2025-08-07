package vercors.sif.unverifedcode.examples.implicit;

class A {
    int i;
    A a;
}

class HighConstructorCall {
    //insecure!
    // constructor calls should be lowEvent. Otherwise it might be possible for the adversary to infer
    // secret information from the hashcode from any low created object (depending how many objects have been created before etc.)
    //@ requires lowEvent;
    public void main(boolean secret) {
        A a;
        if (secret) {
            a = new A();
        } else {
            a = new A();
        }
    }
}
