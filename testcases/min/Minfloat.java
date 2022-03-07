// expected : unsat
import java.util.ArrayList;

public class Minfloat
{

    //@ requires 0 < a.size() < Integer.MAX_VALUE && a != null ;
    //@ ensures \result == (\min int j; 0 <= j && j < a.size(); a.get(j));
    public float listMin(ArrayList<Float> a)
    {
        float min;
        min = a.get(0);
        
        //@ loop_invariant 0 <= i <= a.size();
        //@ loop_invariant min == (\min int j; 0 <= j && j < i; a.get(j));
        for(int i = 0; i < a.size(); i++)
        {
            if(a.get(i) < min)
            {
                min = a.get(i);
            }
        }
        
        return min;
    }

    
}