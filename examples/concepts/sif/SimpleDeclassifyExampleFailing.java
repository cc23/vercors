public class SimpleDeclassifyExampleFailing {

    /*@
      ensures low(\result);
    @*/
    public int test(int x) {
        //@ declassify(x/2)
        return x;
    }

}