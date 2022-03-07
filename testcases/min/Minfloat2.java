// expected : unsat

public class Minfloat2
{

    //@ requires 0 < a < 5;
    //@ ensures \result == (\min float j; 0 <= j && j < a; j);
    public float listMin(float a)
    {
        float min;
        // assert min == 0;
        min = 0;
        //@ loop_invariant min == 0;
        //@ loop_invariant 0 <= i <= a + Float.MIN_VALUE;
        //@ loop_invariant min == (\min float j; 0 <= j && j < i; j);
        for(float i = 0; i < a; i+=Float.MIN_VALUE)
        {
            if(i < min)
            {
                min = i;
            }
        }
        
        return min;
    }
  
}