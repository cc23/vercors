class MyException extends Exception {
}

class MyException2 extends Exception {
}

class Container{
    public int value;
    /*@
    ensures Perm(value, 1);
    @*/
    public Container() {
        this.value = 0;
    }
}
public class TestTryCatch {

    /*@
        ensures b ==> \result == -2;
        ensures !b ==> \result == 2;
    @*/
    public int m1(boolean b) {
        int x;

        try {
            if (b)
                throw new MyException();
            else
                x = 1;
        } catch (MyException exception) {
            x = -1;
        } finally {
            x *= 2;
        }
        return x;
    }

    /*@
          ensures b ==> \result == -2;
          ensures !b ==> \result == 0;
    @*/
    public int m3(boolean b) {
        int x = 0;

        try {
            if (b)
                throw new MyException();
        } catch (MyException exception) {
            x = -1;
        } finally {
            x *= 2;
        }
        return x;
    }

    /*@
          requires low(i);
          requires Perm(c.value, 1);
          ensures Perm(c.value, 1);
          ensures low(c.value);
          ensures i == 0 ==> c.value == 0;
          ensures i < 0 ==> c.value == -1;
          ensures i > 0 ==> c.value == 1;
    @*/
    public void m6(int i, Container c) {
        try{
            if(i < 0){
                throw new MyException();
            } else if (i > 0 ) {
                throw new MyException2();
            } else {
                c.value = 0;
            }
        } catch (MyException myException){
            c.value = -1;
        } catch (MyException2 myException2){
            c.value = 1;
        }
    }



}