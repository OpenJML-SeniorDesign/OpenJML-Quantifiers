(set-option :smt.mbqi true)
; (set-option :verbose  10)


;------------------ Declarations ------------------
; Declaring the type of the array
(declare-sort array 0)

; Declare the sum functions to take an array high and low and return and Int
(declare-fun sum (array Int Int) Int)
(declare-fun s (array Int Int) Int)

; Declare a select function to get the element at an index
(declare-fun getElem (array Int) Int)

; Declare the array as a function that takes nothing and returns the array
(declare-fun inputArr () array)
;------------------ Declarations ------------------

;------------------ Fill Array --------------------
; inputArr = [0, 1, 2, ...]
(assert (forall ((x Int) ) (! (= (getElem inputArr x) 1))))
;------------------ Fill Array --------------------

;------------------ Matching Trigger Setup --------
(assert 
    (forall 
    ((lo Int) (hi Int) (arr array))
    (! (= (sum arr lo hi) (s arr lo hi))
    :pattern ((sum arr lo hi))
    ))
)
;------------------ Matching Trigger Setup --------

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
    :pattern ((s arr lo hi))
    ))
)
;------------------ Unit Axiom --------------------

;------------------ Induction Below ---------------
(assert 
    (forall
    ((lo Int) (hi Int) (arr array))
    (! (=>
        (< lo hi)
        (= (s arr lo hi) (+ (s arr (+ lo 1) hi) (getElem arr lo)))
    )
    :pattern (sum arr lo hi)
    ))
)
;------------------ Induction Below ---------------

;------------------ Induction Above ---------------
(assert 
    (forall
    ((lo Int) (hi Int) (arr array))
    (! (=>
        (< lo hi)
        (= (s arr lo hi) (+ (s arr lo (- hi 1)) (getElem arr (- hi 1))))
    )
    :pattern (sum arr lo hi)
    ))
)
;------------------ Induction Above ---------------

;(assert (not (= (sum inputArr 1 5) 4)))
   
(assert (not (= (sum inputArr 1 6) (sum inputArr 2 7))))   

(check-sat)
