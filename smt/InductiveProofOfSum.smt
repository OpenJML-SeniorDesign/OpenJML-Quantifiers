(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :smt.mbqi true)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
(set-option :verbose  10)


;------------------ Declarations ------------------
; Declaring the type of the array
(declare-sort array 0)

; Declare the sum functions to take an array high and low and return and Int
(declare-fun sum (array Int Int) Int)
(declare-fun s (array Int Int) Int)
;(define-fun sumOfn ((n Int)) Int (div (* n (- n 1)) 2))
(define-fun sumOfn ((n Int)) Int (div (* n (+ n 1)) 2))


; Declare a select function to get the element at an index
(declare-fun getElem (array Int) Int)

; Declare the array as a function that takes nothing and returns the array
(declare-fun inputArr () array)

(declare-const i Int)
;------------------ Declarations ------------------




;------------------ Fill Array --------------------
(assert (forall ((x Int) ) (! (= (getElem inputArr x) x))))
;------------------ Fill Array --------------------

;------------------ Unit Axiom --------------------
(assert 
    (forall
    ((lo Int) (hi Int) (arr array))
    (! (=> 
        (forall
			((k Int) )
			(=>	(and (<= lo k) (< k hi)) (= (getElem arr k) 0))
		)
        (= (s arr lo hi) 0)
    )
    ))
)
;------------------ Unit Axiom --------------------

; inductive deffinition for Sum
; This is generic. Applies to any loop with integer bounds
; What were addingt up is deffined by our function getElem
; Get elem on inputArr as deffined about and hi is hi.
(assert (forall 
	((lo Int) (hi Int) (arr array))
		(= (sum arr lo (+ hi 1)) (ite (< hi lo) 0 (+ (sum arr lo hi) (getElem arr hi))))
))

; can we prove for an integer k that 


(assert (not (forall 
		((k Int)) 
		(=> (>= k 0)
			(=>
		 	(= (sum inputArr 0 k) (sumOfn k)) (= (sum inputArr 0 (+ k 1)) (sumOfn (+ k 1)))
			)
		)
)))	


(check-sat)
