// expected: unsat

public class Min
{

    //@ requires 0 < a.length < Integer.MAX_VALUE && a != null ;
    //@ ensures \result == (\min int j; 0 <= j && j < a.length; a[j]);
    public int arrayMin(int[] a)
    {
        int min;
        min = a[0];

        //@ loop_invariant 0 <= i <= a.length;
        //@ loop_invariant min == (\min int j; 0 <= j && j < i; a[j]);
        for(int i = 0; i < a.length; i++)
        {
            if(a[i] < min)
            {
                min = a[i];
            }
        }
        
        return min;
    }
}