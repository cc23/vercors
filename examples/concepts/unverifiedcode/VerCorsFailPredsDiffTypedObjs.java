//this fails on dev branch

//@ resource hidden(Object x);

class TryThis {
    //@ requires hidden(b);
    //@ requires b != null;
    //@ requires t != null;
    public void main(B b, TryThis t){
        //@ assert perm(hidden(t)) == 0;
    }
}
class B {
    private int f;
}