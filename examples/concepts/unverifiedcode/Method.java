class MethodExample {

    private int f;
    private MethodExample t;

    //@ ensures low(\result);
    public MethodExample f() {
        MethodExample t = new MethodExample();
        //@ inhale leakable(t);
        //@ assert low(t);
        return t;
    }

    public int g(){
        return 3;
    }

    //fails -> t not low
    public int getF() {
        //@ inhale Perm(f, read);
        return f;
    }

    //fails -> t not leakable
    public MethodExample getT(){
        //@ inhale Perm(t, read);
        //@ inhale low(t);
        return t;
    }
}