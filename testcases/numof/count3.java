

// expected : Unsat
public class count3
{
    // eval constant expr
	//@ ensures \result == (\num_of int i; 0 <= i && i <= 4; i % 2 == 0);
	public static int n1() {
		//      0   1   2   3   4
		// return  1 + 0 + 1 + 1 + 1;
		return  1 + 0 + 1 + 0 + 1;
	}
}
