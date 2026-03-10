a.
b.

equal(a, b)?
equal(a, a)?
equal(a)?
equal?
equal(X, X)?
equal(X, Y)?

b(X) :- equal(X, t).
b(t)?
b(p)?
a(X) :- unequal(X, t).
a(t)?
a(p)?
