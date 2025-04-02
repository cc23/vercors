class SimpleTryCatch {

    /*@
        ensures low(\result);
     @*/
    public int test(int secret){
        try{
            throw new RuntimeException();
        } catch(Throwable e){
            return 0;
        }
        return secret;
    }
}