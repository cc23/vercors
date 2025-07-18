//@ unverified_class
class A extends VerifiedClass {

    public A(){}

    public int f(int secret);
    public int g(int secret);
    public void h();
}

class VerifiedClass {

    //@ requires lowEvent;
    public void test(int secret) {
        A a = new A();
        a.f(0);
        a.g(0);
        VerifiedClass t = a;
        // TODO this should to fail
        t.f(secret);
    }

    //@ requires lowEvent;
    public int test2(int secret) {
        A a1 = new A();
        return a1.f(0);
    }

    //this method fails on purpose
    //@ requires lowEvent;
    public void testFail(int secret) {
        A a1 = new A();
        A a2 = new A();
        A a = secret > 0 ? a1 : a2;
        a.h();
    }

    public int f(int secret){
        return 2;
    }
}

