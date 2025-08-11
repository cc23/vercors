class DivideByZeroException extends RuntimeException {

}
//@ uc_invariant Perm(d, read) ** d != 0;
class Main {

    private double d;

    //@ requires d != 0;
    //@ ensures hidden(this);
    //@ ensures Perm(this.d, write) ** this.d == d;
    //@ signals (RuntimeException e) d == 0;
    public Main(double d) {
        if (d == 0){
            throw new RuntimeException();
        }
        this.d = d;
    }

    //@ given boolean isLeakable;
    //@ given boolean indirectlyFromUc;
    //@ requires isLeakable ==> leakable(this);
    //@ requires !isLeakable ==> hidden(this);
    //@ requires lowEvent;
    //@ requires Perm(this.d, read);
    //@ requires !isLeakable ==> d != 0;
    //@ ensures isLeakable ==> leakable(this);
    //@ ensures !isLeakable ==> hidden(this);
    private double test() {
        Divisor divisor = new Divisor();
        double tmp = this.d;
        return divisor.divide(1, tmp) /* @ given {indirectlyFromUc=indirectlyFromUc} @*/ ;
    }
}


class Divisor{

    //@ given boolean indirectlyFromUc;
    //@ requires lowEvent;
    //@ requires !indirectlyFromUc ==> d2 != 0;
    //@ signals (DivideByZeroException e) d2 == 0;
    //@ ensures low(d1) && low(d2) ==> low(\result);
    //@ ensures d2 != 0 ==> \result*d2 == d1;
    public double divide(double d1, double d2){
        DivideByZeroException exception = new DivideByZeroException();
        if(d2 == 0){
            throw exception;
        }
        return d1 / d2;
    }
}