// expected: UNsat

public class Multarray
{
    // eval prod of array
	//@ requires 0 < arr.length < 4;
	//@ ensures \result == (\product int i; 0 <= i && i < arr.length; arr[i]);
	public static int p3(int[] arr) {
		int total = 1;

		//@ maintaining 0 <= j <= arr.length;
		//@ maintaining total == (\product int i; 0 <= i && i < j; arr[i]);
		//@ decreasing arr.length - j;
		for (int j = 0; j < arr.length; j++) {
			//@ assume Integer.MIN_VALUE <= total * arr[j] <= Integer.MAX_VALUE; // Just assume we never overflow
			total *= arr[j];
		}

		return total;
	}
}   
   