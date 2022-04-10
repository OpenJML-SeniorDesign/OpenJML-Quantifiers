
// expected : Unsat

public class RangeFilter
{
    //@ ensures \result == (\sum int i; 1 < i < 5 && i % 2 == 0; i);
	public static int rangeAndFilterConstant() {
		return  2 + 4;
	}
}

