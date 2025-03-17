class MyException extends Exception {
}

public class TestTryCatchFailing {

    /*@
            ensures b ==> \result == -2;
            ensures !b ==> \result == 2;
     @*/
    public int m2(boolean b) {
        //should fail with post condition violated
        int x;

        try {
            if (b)
                throw new MyException();
            else
                x = 2;
        } catch (MyException exception) {
            x = -1;
        } finally {
            x *= 2;
        }
        return x;
    }
}