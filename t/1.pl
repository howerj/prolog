% https://stackoverflow.com/questions/8966488/prolog-and-ancestor-relationship?rq=3
mother(anna, fanny).
mother(daniel, fanny).
mother(celine, gertrude).
father(tim, bernd).
father(anna, ephraim).
father(daniel, ephraim).
father(celine, daniel).

ancestor(X, Y, Z) :- ancestor(X, Y, X, Z).
ancestor(X, Y, Acc, father(Acc)) :- father(X, Y).
ancestor(X, Y, Acc, mother(Acc)) :- mother(X, Y).
ancestor(X, Y, Acc, Result) :- father(X, Z), ancestor(Z, Y, father(Acc), Result).
ancestor(X, Y, Acc, Result) :- mother(X, Z), ancestor(Z, Y, mother(Acc), Result).

?- ancestor(ephraim, tim, X).
