fof(p1, axiom, p <=> (
	(![X]: ((s(X) & t(X)) => r(X)))
	=>
	(?[X]: (s(X) & ~t(X)))
)).

fof(q1, axiom, q <=> (
	(![X]: (s(X) => t(X)))
	|
	(![X]: (s(X) => r(X)))
)).
fof(r1, axiom, r <=> (
	(![X]: ((s(X) & r(X)) => t(X)))
	=>
	(?[X]: (s(X) & t(X) & ~r(X)))
)).
fof(f, conjecture, (p & q) => r).
