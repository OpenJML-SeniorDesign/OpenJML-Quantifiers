// expected : Unsat

public class nested
{
    //@ ensures \result == (\sum int i; 0 < i && i < 3; (\sum int j; 0 < j && j < i; i+j));
	public static int nest() {
		return  3;
	}
}