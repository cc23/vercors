package vercors.sif.unverifedcode.examples.explicit;

//@ unverified_class
class UnverifiedClass{
    public void unverifiedFunction(Object o);
}

//@ uc_invariant leakable(object) ** low(object);
class GetterTransitive {
    // inv: low(object) && leakable(object)
    public int f;
    //@ modifiable
    private GetterTransitive object;

    //@ ensures hidden(this);
    //@ ensures Perm(this.f, write);
    //@ ensures Perm(this.object, write);
    //@ ensures this.f == 0;
    //@ ensures this.object == null;
    //@ ensures leakable(object);
    public GetterTransitive(){

    }

    //@ requires leakable(this);
    //@ ensures leakable(this);
    public GetterTransitive getObject() {
        return this.object;
    }

    //insecure
    //@ requires lowEvent;
    public void leakSecretObject(int secret) {
        UnverifiedClass uc = new UnverifiedClass();
        GetterTransitive myObject = new GetterTransitive();
        //@ leak(myObject)
        uc.unverifiedFunction(myObject);
        GetterTransitive my2ndLayerObject = new GetterTransitive();
        my2ndLayerObject.f = secret;
        //insecure
        //@ leak(my2ndLayerObject)
        myObject.object = my2ndLayerObject;
    }

}