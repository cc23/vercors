class ReturnLoopExample {

    /*@
        ensures low(\result);
     @*/
    public int test(boolean secret) {
        int x = 0;
        //@ loop_invariant 1 <= i && i <= 10;
        //@ loop_invariant x == i-1;
        for (int i = 1; i < 10; i++) {
            if(secret){
                return 9;
            }
            x = i;
        }
        return x;
    }
}