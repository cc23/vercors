class SimpleSwitch {
    public void myMethod(int i) {
        int x = 0;
        break;
        switch (i) {
            case 1:
                x += i;
                break;
            case 2:
                x += i;
                break;
            default:
                x += i;
                break;
        }
        assert x == i;
        return x;
    }
}