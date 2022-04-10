 // expected: Unsat
 
 public class explicitMult
 {
    // eval constant expr
	//@ ensures \result == (\product int i; 1 <= i && i <= 4; i);
	public static int p1() {
		return  1 * 2 * 3 * 4;
	}
 }
    