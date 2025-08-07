package vercors.sif.unverifedcode.examples.implicit;
// Adversary defined subclasses do not pose a problem for field assigns
public class UnverifiedReceiverFieldAssign {
    private int concealedField;
    private int concealedField2;
    public static void storeSecretInConcealedField(UnverifiedReceiverFieldAssign unverifiedReceiverFieldAssign, int secret) {
        unverifiedReceiverFieldAssign.concealedField = secret;
    }
    public static void storeSecretInConcealedField2(UnverifiedReceiverFieldAssign unverifiedReceiverFieldAssign, int secret) {
        unverifiedReceiverFieldAssign.concealedField2 = secret;
    }
}

class UnverifiedSubClass extends UnverifiedReceiverFieldAssign{
    private int concealedField;
    public int concealedField2;
    public static void main(String[] args) {
        UnverifiedSubClass unverifiedSubClass = new UnverifiedSubClass();

        storeSecretInConcealedField(unverifiedSubClass, 11);
        System.out.println(unverifiedSubClass.concealedField);

        storeSecretInConcealedField2(unverifiedSubClass, 11);
        System.out.println(unverifiedSubClass.concealedField2);
    }
}