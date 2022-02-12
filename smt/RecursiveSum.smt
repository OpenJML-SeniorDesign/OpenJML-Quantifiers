; recursive version of sum

; with mbqi, incorrect code produces sat
; without mbqi, incorrect code produces unknown with reason incomplete quantifiers
(set-option :smt.mbqi true)

; Array type
(declare-sort array 0)

; Array indexing
(declare-fun getElem (array Int) Int)

; sum(lo, hi, aa) == (hi < lo) ? 0 : sum(lo, hi - 1) + aa[hi];
(define-fun-rec sum ((lo Int) (hi Int) (aa array)) Int (ite (< hi lo) 0 (+ (sum lo (- hi 1) aa) (getElem aa hi))))

; sum of n positive integers == n*(n+1)/2;
(define-fun sumOfn ((n Int)) Int (div (* n (+ n 1)) 2))

; sum of n positive integers with a bug
(define-fun sumOfnBuggy ((n Int)) Int (div (* n (- n 1)) 2))

; array constant of [0, 1, 2, ...]
(declare-fun arr () array)
(assert (forall ((x Int)) (= (getElem arr x) x)))

; array constant with unknown values
(declare-fun blankArr () array)

; expected unsat
(push 1)
(echo "show sum(1, 3, arr) == arr[1] + arr[2] + arr[3]")
(assert
	(not
		(= 
			(sum 1 3 blankArr)
			(+
				(+
					(getElem blankArr 1)
					(getElem blankArr 2)
				)
				(getElem blankArr 3)
			)
		)
	)
)
(check-sat)
(echo "")
(pop 1)

; expected unsat
(push 1)
(echo "show sum of n + 1 == sum(0, n + 1) if sum of n == sum(0, n)")
(assert
	(not
		(forall 
			((k Int)) 
			(=>
				(>= k 0)
				(=>
		 			(= (sum 0 k arr) (sumOfn k)) (= (sum 0 (+ k 1) arr) (sumOfn (+ k 1)))
				)
			)
		)
	)
)
(check-sat)
(echo "")
(pop 1)

; expected sat with mbqi, otherwise unknown
(push 1)
(echo "show buggy sum of n does not always equal sum(0, n + 1)")
(assert
	(not
		(forall 
			((k Int)) 
			(=>
				(>= k 0)
				(=>
		 			(= (sum 0 k arr) (sumOfnBuggy k)) (= (sum 0 (+ k 1) arr) (sumOfnBuggy (+ k 1)))
				)
			)
		)
	)
)
(check-sat)
(get-info :reason-unknown)
(echo "")
(pop 1)

; this is slow, expected unsat
(push 1)
(echo "show sum of ints from 101 to 1000 is 495450")
(assert
	(not
		(= 
			(sum 101 1000 arr)
			495450
		)
	)
)
(check-sat)
(echo "")
(pop 1)
