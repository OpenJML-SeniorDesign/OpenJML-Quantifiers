// expected: Unsat
// result: 

public class AlwaysFalseRangeUnsat {

    //@ ensures \result == (\product int i; false; i*100);
    public static double AlwaysFalseRange() {
        return 1;
    }

}