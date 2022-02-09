public class Sum {

    /*@ public normal_behavior
      @   requires (\sum int i; 0 <= i && i < arr.length; arr[i]) < Integer.MAX_VALUE;
      @   ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @*/
    public int sum(int [] arr) {
        int total = 0;
        int k = 0;
        //@ maintaining 0 <= k && k <= arr.length;
        //@ maintaining total == (\sum int j; 0 <= j && j < k; arr[j]);
        //@ decreasing arr.length - k;
        while (k < arr.length) {
            total += arr[k];
            k++;
        }
        //@ assert total == (\sum int j; 0 <= j && j < arr.length; arr[j]);
        return total;
    }
}
