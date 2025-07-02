class A{
    public int x;


    //@ requires other instanceof A ==> Perm(((A)other).x, read);
    //@ requires Perm(this.x, read);
    @Override
    public boolean equals(Object other){
        return other instanceof A && x == ((A)other).x;
    }
}
class LowObjects{

    public void main(int secret){
        A a1 = new A();
        A a2 = new A();
        A a = secret > 0 ? a1 : a2;
        //@assert low(a);
    }
}