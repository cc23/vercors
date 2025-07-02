// should pass

class BreakFinally {
    public int test() {
        boolean x = true;
        for (int i = 1; i < 10; i++) {
            try{
                if (x) {
                    break;
                }
            } finally {
               assert true;
            }
            assert false;
        }

    }
}