//should pass

public class JoanaFig1Fixed {

    /*@
        requires lowEvent;
    @*/
    public void print(int val) {

    }

    public int inputPIN() {
        return 17;
    }

    /*@
        requires lowEvent;
    @*/
    public void main() {
        int x = inputPIN();
        //@ declassify(x < 1234)
        if (x < 1234) {
            print(0);
        }
        int y = x;
        //@ declassify(x)
        print(y);
    }
}