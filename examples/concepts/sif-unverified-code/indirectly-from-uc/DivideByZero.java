class DivideByZeroException extends RuntimeException {

    public DivideByZeroException() {

    }
}

class Main {

    //@ requires lowEvent;
    //@ requires d != 0;
    //@ signals (DivideByZeroException e) d == 0;
    public double test(double d) {
        return divide(1, d) /* @ given {indirectlyFromUc=true} @*/ ;
    }

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
