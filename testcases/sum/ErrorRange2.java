

// expected : Sat
public class ErrorRange2
{
    //@ ensures \result == (\sum int i; i < i && i > i; i);
	public static int badRange2() {
		return  2 + 4;
	}
}