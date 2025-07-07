// should fail on line 8
class SimpleHidden {
    public int test(int secret) {
        SimpleHidden x = new SimpleHidden();
        //@ inhale hidden(x, 1);
        //@ assert hidden(x, 1);
        //@ exhale hidden(x, 1);
        //@ assert hidden(x, 1);
    }
}