// expected: Unsat
// result: 

public class SimpleUnsat {
	//@ requires 0 < n < 100;
	//@ ensures \result == (\product int i; 0 <= i && i < n; i);
	public static int p(int n) {
		int total = 0;

		//@ maintaining 0 <= j <= n;
		//@ maintaining total == (\product int i; 0 <= i && i < j; i);
		//@ decreasing n - j;
		for (int j = 0; j < n; j++) {
			//@ assume Integer.MIN_VALUE <= total * j <= Integer.MAX_VALUE; // assume no overflow/underflow
			total *= j;
		}

		return total;
	}
}