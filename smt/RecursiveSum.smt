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
(assert (forall ((x Int)) (! (= (getElem arr x) x))))

; array constant with unknown values
(declare-fun blankArr () array)

; show sum(0, 1, blankArr) == blankArr[0] + blankArr[1]
(push)
(assert
	(not
		(= 
			(sum 0 1 blankArr)
			(+
				(getElem blankArr 0)
				(getElem blankArr 1)
			)
		)
	)
)
(check-sat)
(pop)

; expected unsat
(push)
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
(pop)

; expected sat with mbqi, otherwise unknown
(push)
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
(pop)
