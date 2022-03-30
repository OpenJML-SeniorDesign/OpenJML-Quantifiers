// expected: sat
// result: sat

public class OverflowShortSat {
	
	//@ requires 0 < n < 100;
	//@ ensures \result == (\sum short i; 0 <= i && i < n; i*i*i*i);
	public static short s(int n) {
		short total = 0;

		//@ maintaining 0 <= j <= n;
		//@ maintaining total == (\sum short i; 0 <= i && i < j; i*i*i*i);
		//@ decreasing n - j;
		for (short j = 0; j < n; j++) {
			//@ assume Short.MIN_VALUE <= total + j <= Short.MAX_VALUE; // assume no overflow/underflow
			total += (j*j*j*j);
		}
		
		return total;
	}
}