// should pass
// failed before implementing SIFTryCatchStmt
class MyException extends Exception {}
class FinallyBreak {
    public int test() {
        boolean x = true;
        for (int i = 1; i < 10; i++) {
            try{
                if (x) {
                    break;
                }
                throw new MyException();
            } catch (Exception e){
                assert false;
            }
            finally {
               assert true;
            }
            assert false;
        }

    }
}