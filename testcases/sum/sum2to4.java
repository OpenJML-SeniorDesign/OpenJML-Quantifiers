
//expected : Unsat

public class sum2to4
{
    // eval a constant expr
	//@ ensures \result == (\sum int lo; 1 < lo < 5; lo);
	public static int s1() {
		return  2 + 3 + 4;
	}
}