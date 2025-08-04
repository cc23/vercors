//@ uc_invariant Perm(password, read);
class PasswordChecker {
    // conc = {password}

    private int password;

    // this precondition is only needed for "timing attacks"
    //@ requires low(toLowerCase) && low(toUpperCase);
    //@ ensures Perm(this.password, write);
    //@ ensures !toLowerCase && !toUpperCase ==> password == this.password;
    //@ ensures hidden(this);
    public PasswordChecker(int password, boolean toLowerCase, boolean toUpperCase) {
        int modifiedPassword;
        if (toLowerCase) {
            modifiedPassword = toLowerCase(password);
        } else if (toUpperCase) {
            modifiedPassword = toUpperCase(password);
        } else {
            modifiedPassword = password;
        }
        this.password = modifiedPassword;
    }

    //@ requires Perm(this.password, write);
    //@ requires hidden(this);
    //@ ensures Perm(this.password, write);
    //@ ensures \result ==> password == this.password;
    public boolean checkPassword(int password) {
        int correctPw = this.password;
        boolean correct = correctPw == password;
        //@ declassify(correct)
        return correct;
    }

    //@ requires Perm(this.password, 1/2);
    //@ ensures Perm(this.password, 1/2);
    private int toLowerCase(int password);

    //@ requires Perm(this.password, 1/2);
    //@ ensures Perm(this.password, 1/2);
    private int toUpperCase(int password);
}
