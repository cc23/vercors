class ReturnExample {

    /*@
        ensures low(\result);
     @*/
    public int test(int secret){
        int x = secret - secret + 2;
        if(secret > 3){
            return x;
        } else {
            return x;
        }
    }
}