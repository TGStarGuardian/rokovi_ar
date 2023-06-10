(set-logic QF_LIA)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun x7 () Int)
(declare-fun x8 () Int)

(declare-fun y1 () Int)
(declare-fun y2 () Int)
(declare-fun y3 () Int)
(declare-fun y4 () Int)
(declare-fun y5 () Int)
(declare-fun y6 () Int)
(declare-fun y7 () Int)
(declare-fun y8 () Int)



(assert (and
	(<= 1 x1 8)
	(<= 1 x2 8)
	(<= 1 x3 8)
	(<= 1 x4 8)
	(<= 1 x5 8)
	(<= 1 x6 8)
	(<= 1 x7 8)
	(<= 1 x8 8)
	(<= 1 y1 8)
	(<= 1 y2 8)
	(<= 1 y3 8)
	(<= 1 y4 8)
	(<= 1 y5 8)
	(<= 1 y6 8)
	(<= 1 y7 8)
	(<= 1 y8 8)
	
	(distinct x1 x2 x3 x4 x5 x6 x7 x8)
	(distinct y1 y2 y3 y4 y5 y6 y7 y8)
	
	; za dijagonale
	; napadaju se samo ako je koef pravca
	; 1 ili -1
	; dakle, |yp - yq| = |xp - xq|
	; yp - yq = xp - xq
	; tj. yp - xp = yq - xq
	; ili
	; yp - yq = xq - xp
	; tj. yp + xp = xq + yq
	
	(distinct (+ x1 y1) (+ x2 y2) (+ x3 y3) (+ x4 y4) (+ x5 y5) (+ x6 y6) (+ x7 y7) (+ x8 y8))
	(distinct (- x1 y1) (- x2 y2) (- x3 y3) (- x4 y4) (- x5 y5) (- x6 y6) (- x7 y7) (- x8 y8))
	
	; jedna je na a1...neka to bude dama 1
	(= x1 1)
	(= y1 1)

	)
)

(check-sat)
(get-value (x1 y1))
(get-value (x2 y2))
(get-value (x3 y3))
(get-value (x4 y4))
(get-value (x5 y5))
(get-value (x6 y6))
(get-value (x7 y7))
(get-value (x8 y8))
(exit)













