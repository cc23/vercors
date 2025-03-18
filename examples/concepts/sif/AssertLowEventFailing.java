class AssertLowEventFailing {
    /*@
        requires lowEvent;
     @*/
    public int myMethod(int y) {
        int x = 3;
        if(y < x){
            //@ assert lowEvent;
        }
        return x;
    }
}