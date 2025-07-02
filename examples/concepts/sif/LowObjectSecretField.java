class A{
    public int x;
}
class LowObjects{
    //@ requires low(aParam);
    //@ requires Perm(aParam.x, write);
    public void main(A aParam , int secret){
        aParam.x = secret;
        //@assert low(aParam);
    }
}