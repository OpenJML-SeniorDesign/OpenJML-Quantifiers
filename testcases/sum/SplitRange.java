// expected: unsat

public class SplitRangeUnsat {
	//@ requires 0 < n < 100;
	//@ requires 0 < k < k;
	//@ ensures \result == (\sum int i; 0 <= i && i < n && i != k; i);
	public static int s(int n, int k) {
		int total = 0;

		//@ maintaining 0 <= j <= n;
		//@ maintaining total == (\sum int i; 0 <= i && i < j && j != k; i);
		//@ decreasing n - j;
		for (int j = 0; j < n; j++) {
			//@ assume Integer.MIN_VALUE <= total + j <= Integer.MAX_VALUE; // assume no overflow/underflow
			if (j!=k) total += j;
		}

		return total;
	}
}

