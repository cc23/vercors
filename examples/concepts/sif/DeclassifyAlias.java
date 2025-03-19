public class DeclassifyAlias {

    /*@
      ensures low(\result);
    @*/
    public int test(int x) {
        int y = x;
        //@ declassify(y)
        return x;
    }

}