class A {
    //inv low(f);
    private int f;

    //@ requires Perm(first.f, write);
    //@ requires Perm(second.f, write);
    //@ requires first.f == 1 && second.f == 2;
    //@ requires lowEvent;
    public void myMethod2(A first, A  second, int secret) {
        A highA = first;
        if(secret > 0){
            highA = second;
        }
        if(secret > 0){
            highA.f = 2;
        } else {
            highA.f = 1;
        }
    }

    //@ requires Perm(first.f, write);
    //@ requires lowEvent;
    public void myMethod1(A first, int secret) {
        if(secret > 0){
            first.f = 2;
            //@ assert low(first.f);
        }
    }
}