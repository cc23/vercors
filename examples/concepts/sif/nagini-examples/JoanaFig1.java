//should fail

public class JoanaFig1 {

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
        if (x < 1234) {
            print(0);
        }
        int y = x;
        print(y);
    }
}