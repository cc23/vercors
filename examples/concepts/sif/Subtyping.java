// testing behavioral subtyping
// should fail if behavioral subtyping is supported

class A {
    /*@
       ensures low(\result);
       ensures \result == 2;
    @*/
    public int getValue(){
        return 2;
    }
}

class B extends A {
    /*@
       ensures \result == 1;
    @*/
    @Override
    public int getValue(){
        return 1;
    }
}

public class Subtyping {

    public int test(int x) {
       A obj = new B();
       assert obj.getValue() == 2;
    }


}