class A {
    //inv low(f);
    private int f;

    // TODO make this work for the default constructor
    //@ ensures low(this);
    //@ ensures Perm(this.f, write);
    public A() {
    }

    //@ requires Perm(a.f, write);
    //@ requires Perm(a2.f, write);
    //@ requires low(a) && low(a2);
    //@ requires lowEvent;
    public void myMethod(A a, A  a2, int secret) {
        a.f = 1;
        A highA = a;
        if(secret > 0){
            highA = a2;
        }
        highA.f = 3;
    }

    //@ requires Perm(a.f, write);
    //@ requires Perm(a2.f, write);
    //@ requires a.f == 1 && a2.f == 2;
    //@ requires lowEvent;
    public void myMethod2(A a, A  a2, int secret) {
        A highA = a;
        if(secret > 0){
            highA = a2;
        }
        if(secret > 0){
            highA.f = 2;
        } else {
            highA.f = 1;
        }
    }
}