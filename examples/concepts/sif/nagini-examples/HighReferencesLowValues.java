public class HighReferencesLowValues {
    /*@
        requires low(i);
        ensures low(\result);
    @*/
    public int add_zero(int i, int secret) {
        if(secret == 0) {
            return i + 0;
        }
        return i;
    }
}