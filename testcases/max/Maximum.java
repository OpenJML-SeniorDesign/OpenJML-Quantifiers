	
public class Maximum
{
    //@ requires 1 < array.length <= Integer.MAX_VALUE;
	//@ ensures (\max int j; 0 <= j < array.length; array[j]) == \result;
	public static int max(int[] array) {
		int currentMax = array[0];

		//@ maintaining 0 <= i <= array.length;
		//@ maintaining (\max int j; 0 <= j < i; array[j]) == currentMax;
		//@ decreasing array.length - i;
		for (int i = 1; i < array.length; i++) {
			if (array[i] > currentMax) {
				currentMax = array[i];
			}
		}

		return currentMax;
	}
}    
    