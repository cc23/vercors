//TODO break/continue with labels
// passes on dev
class BreakLblExample {
    /*@
         ensures \result == 9;
      @*/
    public int test(int secret) {
        int x = 0;
        outer:
        //@ loop_invariant 1 <= i && i <= 10;
        //@ loop_invariant x == i-1;
        for (int i = 1; i < 10; i++) {
            //@ loop_invariant 0 <= j && j <= 1;
            //@ loop_invariant x == i - 1 + j;
            for (int j = 0; j < 1; j++) {
                if (secret % 2 == 0) {
                    break outer;
                }
                x = i;
            }
        }
        if (secret % 2 == 0) {
            return 9;
        }
        return x;
    }
}