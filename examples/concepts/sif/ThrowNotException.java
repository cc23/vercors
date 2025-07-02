class A extends RuntimeException {
}

class MyClass {
    /*@
    signals (A a) true;
    @*/
    public void myMethod() {
        throw new A();
    }
}