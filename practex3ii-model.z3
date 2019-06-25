(set-option :produce-models true)


;;; The universe (the elements)
(declare-datatypes () ((Element a b c d)))



;;; The predicates:
(declare-fun IsZero (Element) Bool)              ;; (IsZero x) should be true iff x is the zero element
(declare-fun Successor (Element Element) Bool)   ;; (Successor x y) should be true iff y is the successor of x (x is the predecessor of y)
(declare-fun Sum (Element Element Element) Bool) ;; (Sum x y z) should be true iff x+y=z
(declare-fun Predicate (Element) Bool)



;;; The formulas:


;;; (1) every element has exactly one successor
(	
	assert(
		forall((x Element)) (
			exists((y Element)) (
				and (Successor x y) (forall((z Element)) (
					=> (Successor x z) (= y z)
				))
			)
		)
	)
)


;;; (2) successor relation is asymmetric
(
	assert(
		forall((x Element) (y Element)) (
				=> (Successor x y) (not (Successor y x))
		)
	)
)


;;; (3) there is exactly one zero element
(
	assert (
		exists ((x Element))(
			and (IsZero x) (forall ((z Element))(
				=>(IsZero z)(= z x)))
				)
		)
)


;;; (4) adding the zero element to any other element gives the element again
(
	assert (
		forall ((x Element)(y Element))(
			=>(IsZero y)(Sum x y x)
		)
	)
)

;;; (5) summing is commutative
(
	assert (forall ((x Element) (y Element) (z Element))(
		=> (Sum x y z)(Sum y x z))
	)
)


;;; (6) summing two elements has at most one result
(
	assert (forall ((x Element) (y Element) (z Element) (z2 Element))(
		=> (and (Sum x y z) (Sum x y z2)) (= z z2))
	)
)


;;; (7) if element z is the sum of elements x y, x' is the successor of x, then
;;;     the successor of z is the result of the sum of x' and y
(
	assert(
		forall ((x Element) (xP Element) (y Element) (z Element) (zP Element)) (
			=> (and (Sum x y z) (Successor x xP)) ( => (Successor z zP) (Sum xP y zP) )
		)
	)
)


;;; (8) the predicate holds for an element iff it does not hold for its the successor
(
	assert(
		forall((x Element) (y Element)) (
			=> (Successor x y) (and ( => (not (Predicate y)) (Predicate x)) ( => (Predicate x) (not (Predicate y))))
		)
	)
)


;;; (9) the zero element satisfies the predicate
(
	assert (exists ((x Element))(
		and (IsZero x) (Predicate x))
	)
)


;;; (10) the sum of every element by itself does not satisfy the predicate
(assert (exists ((x Element) (y Element)) (and (Sum x x y) (not (Predicate y)))))


(check-sat)
;Since, unsat returned and commenting any satement gives sat so the solution confirms "unsatisfied"
;(get-model)
