fof(a1, axiom, a <=> 
	(
	(![X]: ((p(X) & q(X)) => r(X)))  
	=>
	(?[X]: (p(X) & ~q(X)))
	)
).
fof(b1, axiom, b <=> 
	(
	(![X]: (p(X) => q(X)))  
	|
	(![X]: (p(X) => r(X)))
	)
).
fof(c1, axiom, c <=> 
	(
	(![X]: ((p(X) & r(X)) => q(X)))  
	=>
	(?[X]: (p(X) & q(X) & ~r(X)))
	)
).
fof(f, conjecture, (a & b) => c).
