
// expected : Sat

public class ErrorRange
{
    //@ ensures \result == (\sum int i; i % 2 == 1 && i % 2 == 0; i);
	public static int badRange() {
		return  2 + 4;
	}
}