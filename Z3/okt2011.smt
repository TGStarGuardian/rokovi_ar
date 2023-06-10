(set-logic QF_LIA)
(declare-const S Int)
(declare-const E Int)
(declare-const N Int)
(declare-const D Int)
(declare-const M Int)
(declare-const O Int)
(declare-const R Int)
(declare-const Y Int)


(assert
	(and
		(<= 1 S 9)
		(<= 1 M 9)
		(<= 0 E 9)
		(<= 0 N 9)
		(<= 0 D 9)
		(<= 0 O 9)
		(<= 0 R 9)
		(<= 0 Y 9)
		(= (+ (* 1000 S) (* 100 E) (* 10 N) (* 1 D) (* 1000 M) (* 100 O) (* 10 R) (* 1 E)) (+ (* 10000 M) (* 1000 O) (* 100 N) (* 10 E) (* 1 Y)))
		)
	
	
	
)


(check-sat)
(get-value (S E N D))
(get-value (M O R E))
(get-value (M O N E Y))
(exit)
