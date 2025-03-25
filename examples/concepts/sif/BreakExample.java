//passes
// failed before using SIFBreakStatement

class BreakExample {
    /*@
        ensures \result == 9;
      @*/
    public int test(int secret) {
        int x = 0;
        //@ loop_invariant i <= 10;
        //@ loop_invariant x == i-1;
        for (int i = 1; i < 10; i++) {
            if (secret % 2 == 0) {
                break;
            }
            x = i;
        }
        if (secret % 2 == 0) {
            return 9;
        }
        return x;
    }
}