; recursive version of product

; with mbqi, incorrect code produces sat
; without mbqi, incorrect code produces unknown with reason incomplete quantifiers
(set-option :smt.mbqi true)

; Array type
(declare-sort array 0)

; Array indexing
(declare-fun getElem (array Int) Int)

; product(lo, hi, aa) == (hi < lo) ? 0 : product(lo, hi - 1) * aa[hi];
(define-fun-rec product ((lo Int) (hi Int) (aa array)) Int (ite (< hi lo) 1 (* (product lo (- hi 1) aa) (getElem aa hi))))


; array constant of [0, 1, 2, ...]
(declare-fun arr () array)
(assert (forall ((x Int)) (= (getElem arr x) x)))

; array constant of [0, 2, 4, ...]
(declare-fun arr2 () array)
(assert (forall ((x Int)) (= (getElem arr2 x)  (* 2 x))))

; array constant with unknown values
(declare-fun blankArr () array)

; expected unsat
(push 1)
(echo "show sum(1, 3, arr) == arr[1] * arr[2] * arr[3]")
(assert
	(not
		(= 
			(product 1 3 blankArr)
			(*
				(*
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

; expected sat

(push 1)
(echo "show sum(1, 3, arr) == arr[1] * arr[2] * arr[3] is sat")
(assert
	
		(= 
			(product 1 3 blankArr)
			(*
				(*
					(getElem blankArr 1)
					(getElem blankArr 2)
				)
				(getElem blankArr 3)
			)
		)
	
)
(check-sat)
(echo "")
(pop 1)



; expected unsat
(push 1)
(echo "show product of ints from 1 to 13 is 6227020800")
(assert
	(not
		(= 
			(product 1 13 arr)
			6227020800
		)
	)
)
(check-sat)
(echo "")
(pop 1)


; expected unsat
(push 1)
(echo "show product of ints from 1 to 5 of array2 is 3840")
(assert
	(not
		(= 
			(product 1 5 arr2)
			3840
		)
	)
)
(check-sat)
(echo "")
(pop 1)

; expected sat
(push 1)
(echo "show product of ints from 1 to 5 of array2 is not 3841")
(assert
	(not
		(= 
			(product 1 5 arr2)
			3841
		)
	)
)
(check-sat)
(echo "")
(pop 1)

