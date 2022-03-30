// expected: Unsat
// result: 

public class AlwaysFalseRangeUnsat {

    //@ ensures \result == (\num_of int i; false; false);
    public static double AlwaysFalseRange() {
        return 0;
    }

}