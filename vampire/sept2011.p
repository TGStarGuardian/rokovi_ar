fof(a11, axiom,
	a1 <=> (![X]: (p(X) => q(X)))
).
fof(a12, axiom,
	a2 <=> (![X]: (q(X) => s(X)))
).
fof(a13, axiom,
	a3 <=> (![X]: (r(X) => s(X)))
).
fof(a14, axiom,
	a4 <=> (![X]: (p(X) | r(X)))
).
fof(a15, axiom, a5 <=> (![X]: s(X))).
fof(f, conjecture, (a1 & a2 & a3 & a4) => a5).
