class ElIf {
    //@ requires low(lowInput);
    public void main(int lowInput, int secret){
        if(0 < lowInput){
            int x = 0;
            int y = x * 2;
        } else if (0 < secret) {
            int x = lowInput * 2;
        }
    }
}