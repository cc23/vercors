public class LowLoopExample {

    /*@
      ensures low(\result);
    @*/
    public int test(int x) {
        int y = 0;
        for (int i = 0; i < x; i++) {
            y++;
        }
        y = 5;
        return y;
    }

}