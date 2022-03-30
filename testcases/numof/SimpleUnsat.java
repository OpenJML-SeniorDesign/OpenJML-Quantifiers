// expected: Unsat
// result: 

public class SimpleUnsat {
	//@ requires 0 < n < 100;
	//@ ensures \result == (\num_of int i; 0 <= i && i < n; true);
	public static int n(int n) {
		int total = 0;

		//@ maintaining 0 <= j <= n;
		//@ maintaining total == (\num_of int i; 0 <= i && i < j; true);
		//@ decreasing n - j;
		for (int j = 0; j < n; j++) {
			//@ assume Integer.MIN_VALUE <= total+1 <= Integer.MAX_VALUE; // assume no overflow/underflow
			total++;
		}

		return total;
	}
}