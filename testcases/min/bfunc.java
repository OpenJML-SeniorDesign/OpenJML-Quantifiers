//expected : unsat

public class bfunc
{

    //@ requires 0 < a.length < Integer.MAX_VALUE && a != null && (\forall int j;  0 <= j && j < a.length; 0 <= a[j] && a[j] < 10000);
    //@ ensures \result == (\min int j; 0 <= j && j < a.length; (a[j] - 5)*(a[j] - 5) + 2);
    public int minf(int [] a)
    {
        int min;
        int [] result = new int[a.length];

        //@ loop_invariant 0 <= i <= a.length;
        //@ loop_invariant (\forall int j; 0 <= j && j < i; result[j] == (a[j] - 5)*(a[j] - 5) + 2);
        for(int i = 0; i < a.length; i++)
        {   
            result[i] = (a[i]-5)*(a[i]-5) + 2;

        }

        min = result[0];

        //@ loop_invariant 0 <= i <= result.length;
        //@ loop_invariant min == (\min int j; 0 <= j && j < i; result[j]);
        for(int i = 0; i < result.length; i++)
        {
            if(result[i] < min)
            {
                min = result[i];
            }
        }
        
        return min;
    }

}