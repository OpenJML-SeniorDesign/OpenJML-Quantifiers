
// expected : Sat

public class sumError
{
    //@ ensures \result == (\sum int i; 1 < i < 5; i);
	public static int errors() {
		return  2 + 3 + 4 + 10;
	}
}

