public class SimpleDeclassifyExample {

    /*@
      ensures low(\result);
    @*/
    public int test(int x) {
        //@ declassify(x)
        return x;
    }

}