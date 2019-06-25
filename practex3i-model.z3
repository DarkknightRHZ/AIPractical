(set-option :produce-models true)

; Defining the predicates:
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)
(declare-fun R (Int Int) Bool)

(
    define-fun a1 () Bool (
        forall ((x Int)) (exists ((y Int)) (P x y))
    )
)

(
    define-fun a2 () Bool (
        forall ((x Int)) (exists ((y Int)) (not (R x y)))
    )
)


(
    define-fun a3 () Bool (
        forall ((x Int)) (
            forall ((y Int)) (
                => (or (P x y) (not (R x y))) (forall ((z Int)) (or (Q x z) ( and (not (P y z)) (R y z))) )
            )
        )
    )
)

(
    define-fun formula () Bool (
        forall ((x Int)) (
            exists ((y Int)) (
                Q x y
            )
        )
    )

)

(assert a1)
(assert a2)
(assert a3)
(assert formula)
(check-sat)
(get-model)
;(assert (not formula)) returns unset but (assert formula) returns sat, so the formula is valid for all the assumptions

