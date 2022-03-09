// expected: sat
// result: sat

public class SimpleSat {
	//@ requires 0 < n < 100;
	//@ ensures \result == (\sum int i; 0 <= i && i < n; i+1);
	public static int s(int n) {
		int total = 0;

		//@ maintaining 0 <= j <= n;
		//@ maintaining total == (\sum int i; 0 <= i && i < j; i);
		//@ decreasing n - j;
		for (int j = 0; j < n; j++) {
			//@ assume Integer.MIN_VALUE <= total + j <= Integer.MAX_VALUE; // assume no overflow/underflow
			total += j;
		}

		return total;
	}
}