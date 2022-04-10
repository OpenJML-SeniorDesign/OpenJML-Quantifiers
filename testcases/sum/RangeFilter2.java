
// expected :  Unsat
public class RangeFilter2
{
    //@ requires 0 < n < 9;
	//@ requires n % 2 == 0;
	//@ ensures \result == (\sum int i; 0 <= i && i < n && i % 2 == 0; i);
	public static int rangeAndFilter(int n) {
		int total = 0;

		//@ maintaining j % 2 == 0;
		//@ maintaining 0 <= j <= n;
		//@ maintaining total == (\sum int i; 0 <= i && i < j && i % 2 == 0; i);
		//@ decreasing n - j;
		for (int j = 0; j < n; j += 2) {
			total += j;
		}

		return total;
	}
}