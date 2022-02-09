int a = 0;

// 1 @ maintaining a == (\sum int i; 0<=i<k; i); 
//@ maintaining a == (k*(k-1)) / 2;
for(k=0; k<n; k++) {
	a = a+k;
}
// in our code
	

//@ assert a == (n*(n-1)) / 2;

// 1 @ assert a == (\sum int k; 0<=k<n; k);

-------------
// How would we translate this into smt ?- Two statements.. one for which n = 0 -- base case.
// 
//@ assert (\sum int k; 0<=k<n; k) == ((n*(n-1)) / 2);
// ---- If we can prove 21 and 22, then we have implicitly proved line 18;
// --- 18 can be converted into the conjunction of 21 and 22; This would need to be individual, but automatic based off what we sum.
//@ assert (\sum int k; 0<=k<0; k) == ((0*(0-1)) / 2);
//@ assert (\sum int k; 0<=k<n; k) == ((n*(n-1)) / 2) ==> (\sum int k; 0<=k<(n+1); k) == (((n+1)*(n)) / 2);