class LowEventExample {

    /*@
       requires lowEvent;
    @*/
    public void print(int i) {

    }
    /*@
        requires lowEvent;
     @*/
    public int myMethod() {
        int x = 3;
        print(3);
        return x;
    }
}