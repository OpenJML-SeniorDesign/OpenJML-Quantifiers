// expected: Unsat


public class CumFreq {
	// public static void main(String[] args) {
		// int[] arr = {1, 2, 3, 4, 5, 6};
		// System.out.println(s(arr, 2, 4));
		
		
	// }
	
	
	//@ requires 0 < low < 100;
	//@ requires 0 < high < 100;
	//@ requires low < high;
	//@ requires high < arr.length;
	//@ ensures \result == (\sum int j; 0 <= j <= high; arr[j]) - (\sum int i; 0 <= i <= low; arr[i]);
	public static int s(int[] arr, int low, int high) {
		int[] cumArr = new int[arr.length];
		cumArr[0] = arr[0]; 

		//@ maintaining 0 <= j < high;
		//@ maintaining cumArr[j] == (\sum int i; 0 <= i <= j; arr[i]);
		//@ decreasing high - j;
		for (int j = 0; j < arr.length-1; j++) {
			//@ assume Integer.MIN_VALUE <= arr[j+1] + cumArr[j] <= Integer.MAX_VALUE; // assume no overflow/underflow
			cumArr[j+1] = (arr[j+1] + cumArr[j]);
		}

		//@ assume Integer.MIN_VALUE <= cumArr[high] - cumArr[low] <= Integer.MAX_VALUE; // assume no overflow/underflow
		return cumArr[high] - cumArr[low];
	}
}