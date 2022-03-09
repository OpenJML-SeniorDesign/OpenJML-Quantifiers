// expected: Unsat
// result: Unsat

public class AlwaysFalseRangeUnsat {

    //@ ensures \result == (\sum int i; false; i*i);
    public static double AlwaysFalseRange() {
        return 0;
    }

}