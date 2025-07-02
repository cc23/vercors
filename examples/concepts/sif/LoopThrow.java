// should pass

class LoopThrow {
    public int test() {
        boolean x = true;
        int y = 100;
        try {
            for (int i = 1; i < 10; i++) {
                if (x) {
                    throw new RuntimeException();
                }
                assert false;
            }
        } catch (RuntimeException e) {
            y = 10;
        } catch (Exception e) {
            y = 6;
        } finally {
            assert y == 10;
        }
    }
}