(set-logic QF_NRA)
(declare-fun Ax () Real)
(declare-fun Ay () Real)
(declare-fun Bx () Real)
(declare-fun By () Real)
(declare-fun Cx () Real)
(declare-fun Cy () Real)
(declare-fun Px () Real)
(declare-fun Py () Real)
(define-fun det ((ax Real) (ay Real) (bx Real) (by Real) (cx Real) (cy Real)) Real (- (* (- by ay) (- cx ax)) (* (- bx ax) (- cy ay))) )

(assert
	(and
		(= Ax 1)
		(= Ay 1)
		(= Bx 5)
		(= By 2)
		(= Cx 3)
		(= Cy 7)
		(= Px 2)
		(= Py 5)
		
		; da bi P bilo unutra, moralo bi biti sa leve
		; ili sa desne strane sve tri prave
		; tj. sa leve strane od AB, BC i CA
		; ili sa desne strane od AB, BC i CA
		; pisemo taj uslov
		; ako izleti SAT, onda je unutra
		; racunamo determinantu
		; ax ay 1
		; bx by 1
		; px py 1
		; treba znak sve tri determinante da bude isti
		; determinanta je:
		; ax ay 1
		; bx-ax by-ay 0
		; px-ax py-ay 0
		; izlazi minus ispred...
		; bx-ax by-ay
		; px-ax py-ay
		; -(bx - ax)(py - ay) + (by - ay)(px - ax)
		(or 
			(and
				(<= (det Ax Ay Bx By Px Py) 0)
				(<= (det Bx By Cx Cy Px Py) 0)
				(<= (det Cx Cy Ax Ay Px Py) 0)
			)
			
			(and
				(>= (det Ax Ay Bx By Px Py) 0)
				(>= (det Bx By Cx Cy Px Py) 0)
				(>= (det Cx Cy Ax Ay Px Py) 0)
			
			)
		
		)

	)

)

(check-sat)
(exit)











