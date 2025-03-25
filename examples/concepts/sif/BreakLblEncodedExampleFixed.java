// BreakLblExample where the break with lables is encoded as break without labels

class BreakLblEncodedExample {
    /*@
         ensures \result == 9;
      @*/
    public int test(int secret) {
        int x = 0;
        //@ loop_invariant 1 <= i && i <= 10;
        //@ loop_invariant secret % 2 != 0 ==> x == i-1;
        for (int i = 1; i < 10; i++) {
            boolean breakOuter = false;
            //@ loop_invariant 0 <= j && j <= 1;
            //@ loop_invariant secret % 2 != 0 ==>  x == i - 1 + j;
            //@ loop_invariant secret % 2 != 0 ==> !breakOuter;
            for (int j = 0; j < 1; j++) {
                if (secret % 2 == 0) {
                    breakOuter = true;
                    break;
                }
                x = i;
            }
            if (breakOuter) {
                break;
            }
        }
        if (secret % 2 == 0) {
            return 9;
        }
        return x;
    }
}