
// expected : unsat
import java.util.*;
import java.io.*;
import java.lang.*;

public class TestMin
{
     
     //@ ensures \\result == (\min int j; m <= j && j < p; 2*j - m);
    public static int min(int m, int p)
    {
        if(m >= p)
        {
            //@ assert p <= m;
            return Integer.MAX_VALUE;
        }
        int min = m;

        //@ loop_invariant m <= i <= p + 1;
        //@ loop_invariant min == m;
        //@ loop_invariant min == (\min int j; m <= j && j < p; 2*j - m);
        
        for(int i = m; i < p; i = i + 2)
        {
            min = (i < min ? i : min);

            if(i == Integer.MAX_VALUE - 1)
            {
                break;
            }

        }
        
        return min;

    }

}