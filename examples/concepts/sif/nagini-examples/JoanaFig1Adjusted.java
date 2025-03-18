public class JoanaFig1Adjusted {

    /*@
        requires lowEvent;
    @*/
    public void print(int val){

    }

    public int inputPIN(){
        return 17;
    }

    /*@
        requires lowEvent;
    @*/
    public void main() {
        int x = inputPIN();
        if(x < 1234){
            print(0);
        } else {
            int y = x;
            print(0);
        }
    }
}