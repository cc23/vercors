

class BreakExampleBreakAfterAssign {
    /*@
        ensures \result == 9;
      @*/
    public int test(int secret) {
        int x = 0;
        //@ loop_invariant i <= 10;
        //@ loop_invariant secret % 2 != 0 ==> x == i-1;
        for (int i = 1; i < 10; i++) {
            x = i;
            if (secret % 2 == 0) {
                break;
            }
        }
        if (secret % 2 == 0) {
            return 9;
        }
        return x;
    }
}