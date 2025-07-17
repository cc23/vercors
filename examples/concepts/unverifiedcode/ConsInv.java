class TryThis {
    public TryThis() {
    }
    //@ requires lowEvent;
    public void f(int secret) {
        TryThis t = new TryThis();
        //@ assert low(t);
        //@ inhale leakable(t);
        A a = new A(t);
    }

}

//@ unverified_class
class A extends TryThis {
    public A(int secret, int x, int a, int b, int c){}
    public A(TryThis t){}
}